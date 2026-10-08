import Jsp000404.SixWeakOuterReplay

/-! SOURCE_ONLY remainder literal words; pure Replay Data, no Catalog import. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Jsp404.SixDoubleAllGroup04Data.Mask949
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![true, false, true, false, true, true, false, true, true, true]

def rows : RowsData := ![![4, 2, 1, 3], ![4, 2, 0, 3], ![4, 1, 0, 3], ![4, 0, 1, 2], ![3, 2, 1, 0]]

def localCycle000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, -3, 4, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle001 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -3, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-3, -1, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 3 0]

def localCycle003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 1, .triangle 7 0, .triangle 9 1, .gapLower 3 0, .corridorUpper 2 3, .gapLower 2 3]

def localCycle004 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![0, -3, 0, 0, 1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -2, 4, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 2, .triangle 1 0]

def localCycle006 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -1, -2, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .triangle 3 0]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, -2, 4, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .triangle 6 2, .triangle 1 0]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, 2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 3 0]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![0, -2, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 0 1, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -1, 2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-2, -1, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle013 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -1, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0]

def localCycle014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![0, -3, 0, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 2 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 2, .triangle 1 0]

def localCycle015 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 3 0]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 3 0]

def localCycle018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, -2, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 3 0]

def localCycle020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -1, -3, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle025 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -3, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle026 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-3, -3, -1, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .gapLower 1 4, .triangle 1 0]

def localCycle027 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -1, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -1, 0, 1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle029 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -2, -2, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, -2, -1, -2, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle031 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -1, -2, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -1, -2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, -2, -2, -1, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle034 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -2, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -2, -1, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle036 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-3, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .gapLower 1 4, .triangle 1 0]

def localCycle037 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, -2, -1, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -1, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -1, -3, 4, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -3, -1, 4, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle041 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -3, -1, 0, -1, 3, 0, 0, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 2, .gapLower 0 3]

def localCycle042 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, 0, -1, 3, 0, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 2, .gapLower 0 3]

def localCycle043 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, 0, 1, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, -2, 4, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle045 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -2, -1, -2, 4, 0, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, -2, 4, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -1, -2, 2, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle048 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -2, -2, -1, 4, 0, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, -1, 4, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle050 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, -1, 2, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle051 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -2, -1, 0, -1, 3, 0, 0, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 2, .gapLower 0 3]

def localCycle052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -2, -1, 0, 2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle053 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, 0, 2, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle054 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 2]
    constant := ![-3, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.gapLower 2 2, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4, .triangle 3 1]

def localCycle055 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 1, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, -1, 1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle057 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, -2, 0, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .triangle 1 1]

def localCycle058 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, -2, 0, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .triangle 1 1]

def localCycle059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, -1, 0, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .triangle 1 1]

def localCycle060 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 0 1, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3]

def localCycle061 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 0, 0, 3, -3]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 3]

def localCycle062 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 3 0]

def localCycle063 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -2, 4, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle064 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 3 0]

def localCycle065 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 0, 0, 3, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 3]

def localCycle066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3]

def localCycle067 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, -3, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle068 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -3, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle069 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-2, -3, -1, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .gapLower 1 4, .triangle 1 0]

def localCycle070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle071 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, 0, 1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle072 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -2, -2, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle073 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, -1, -2, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle074 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, -2, 4, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle075 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, -2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle076 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, -2, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle077 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -2, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle078 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -2, 0, -1, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 6 2, .triangle 1 0]

def localCycle079 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .gapLower 1 4, .triangle 1 0]

def localCycle080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, -1, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, -1, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -1, -3, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -3, -1, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle084 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -3, -1, 0, -1, 3, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 2, .gapLower 0 3]

def localCycle085 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, 0, -1, 3, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 2, .gapLower 0 3]

def localCycle086 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, 0, 1, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle087 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, -2, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle088 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -2, -1, -2, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle089 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, -2, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle090 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -1, -2, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle091 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -2, -2, -1, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 2, .triangle 1 2, .gapLower 0 3]

def localCycle092 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, 0, -1, 3, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 2, .gapLower 0 3]

def localCycle093 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, -1, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle094 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, -2, -1, -1, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle095 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, -1, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle096 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.triangle 0 0, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .triangle 1 1]

def localCycle097 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle098 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 0, -1, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle099 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, 0, 0, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 0]

def localCycle100 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, 0, 0, -1, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 0]

def localCycle101 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, 0, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle102 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0]

def localCycle103 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle104 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, -3, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle105 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -3, -1, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle106 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, -3, -1, 4, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .gapLower 1 4, .gapLower 3 2, .gapLower 0 3]

def localCycle107 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, 0, -1, 3, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 6 2, .triangle 1 2, .gapLower 0 3]

def localCycle108 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, 0, 1, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle109 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -2, -2, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle110 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, -2, -1, -2, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 3 2, .gapLower 0 3]

def localCycle111 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, -2, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle112 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, -2, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle113 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, -2, -2, -1, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 2, .triangle 1 2, .gapLower 0 3]

def localCycle114 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -2, -1, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 2, .triangle 1 2, .gapLower 0 3]

def localCycle115 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -2, -1, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle116 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, -2, -1, 4, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .gapLower 1 4, .gapLower 3 2, .gapLower 0 3]

def localCycle117 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, -2, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 3 2, .gapLower 0 3]

def localCycle118 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, -1, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .triangle 1 2, .gapLower 0 3]

def localCycle119 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![0, -1, -3, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3]

def localCycle120 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![-1, -3, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3]

def localCycle121 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![0, -3, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3]

def localCycle122 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, 0, -1, 3, -3, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3, .corridorLower 0 2, .gapLower 0 4, .gapLower 0 3]

def localCycle123 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, -2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3]

def localCycle124 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![0, -2, -1, -2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3]

def localCycle125 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, -2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3]

def localCycle126 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![0, -2, -2, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3]

def localCycle127 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3]

def library : SixWeakOuterReplay.Library
  | 0 => some localCycle000
  | 1 => some localCycle001
  | 2 => some localCycle002
  | 3 => some localCycle003
  | 4 => some localCycle004
  | 5 => some localCycle005
  | 6 => some localCycle006
  | 7 => some localCycle007
  | 8 => some localCycle008
  | 9 => some localCycle009
  | 10 => some localCycle010
  | 11 => some localCycle011
  | 12 => some localCycle012
  | 13 => some localCycle013
  | 14 => some localCycle014
  | 15 => some localCycle015
  | 16 => some localCycle016
  | 17 => some localCycle017
  | 18 => some localCycle018
  | 19 => some localCycle019
  | 20 => some localCycle020
  | 21 => some localCycle021
  | 22 => some localCycle022
  | 23 => some localCycle023
  | 24 => some localCycle024
  | 25 => some localCycle025
  | 26 => some localCycle026
  | 27 => some localCycle027
  | 28 => some localCycle028
  | 29 => some localCycle029
  | 30 => some localCycle030
  | 31 => some localCycle031
  | 32 => some localCycle032
  | 33 => some localCycle033
  | 34 => some localCycle034
  | 35 => some localCycle035
  | 36 => some localCycle036
  | 37 => some localCycle037
  | 38 => some localCycle038
  | 39 => some localCycle039
  | 40 => some localCycle040
  | 41 => some localCycle041
  | 42 => some localCycle042
  | 43 => some localCycle043
  | 44 => some localCycle044
  | 45 => some localCycle045
  | 46 => some localCycle046
  | 47 => some localCycle047
  | 48 => some localCycle048
  | 49 => some localCycle049
  | 50 => some localCycle050
  | 51 => some localCycle051
  | 52 => some localCycle052
  | 53 => some localCycle053
  | 54 => some localCycle054
  | 55 => some localCycle055
  | 56 => some localCycle056
  | 57 => some localCycle057
  | 58 => some localCycle058
  | 59 => some localCycle059
  | 60 => some localCycle060
  | 61 => some localCycle061
  | 62 => some localCycle062
  | 63 => some localCycle063
  | 64 => some localCycle064
  | 65 => some localCycle065
  | 66 => some localCycle066
  | 67 => some localCycle067
  | 68 => some localCycle068
  | 69 => some localCycle069
  | 70 => some localCycle070
  | 71 => some localCycle071
  | 72 => some localCycle072
  | 73 => some localCycle073
  | 74 => some localCycle074
  | 75 => some localCycle075
  | 76 => some localCycle076
  | 77 => some localCycle077
  | 78 => some localCycle078
  | 79 => some localCycle079
  | 80 => some localCycle080
  | 81 => some localCycle081
  | 82 => some localCycle082
  | 83 => some localCycle083
  | 84 => some localCycle084
  | 85 => some localCycle085
  | 86 => some localCycle086
  | 87 => some localCycle087
  | 88 => some localCycle088
  | 89 => some localCycle089
  | 90 => some localCycle090
  | 91 => some localCycle091
  | 92 => some localCycle092
  | 93 => some localCycle093
  | 94 => some localCycle094
  | 95 => some localCycle095
  | 96 => some localCycle096
  | 97 => some localCycle097
  | 98 => some localCycle098
  | 99 => some localCycle099
  | 100 => some localCycle100
  | 101 => some localCycle101
  | 102 => some localCycle102
  | 103 => some localCycle103
  | 104 => some localCycle104
  | 105 => some localCycle105
  | 106 => some localCycle106
  | 107 => some localCycle107
  | 108 => some localCycle108
  | 109 => some localCycle109
  | 110 => some localCycle110
  | 111 => some localCycle111
  | 112 => some localCycle112
  | 113 => some localCycle113
  | 114 => some localCycle114
  | 115 => some localCycle115
  | 116 => some localCycle116
  | 117 => some localCycle117
  | 118 => some localCycle118
  | 119 => some localCycle119
  | 120 => some localCycle120
  | 121 => some localCycle121
  | 122 => some localCycle122
  | 123 => some localCycle123
  | 124 => some localCycle124
  | 125 => some localCycle125
  | 126 => some localCycle126
  | 127 => some localCycle127
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 1, 2, 15, 16, 17, 17, 18, 19, 9, 20, 21, 22, 21, 23], ![24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38], ![39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53], ![0, 1, 54, 55, 56, 57, 6, 58, 8, 9, 59, 11, 12, 13, 60], ![0, 1, 2, 61, 62, 63, 6, 7, 64, 9, 65, 11, 12, 13, 66], ![67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81], ![82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 12, 94, 95], ![0, 1, 2, 55, 56, 5, 6, 96, 8, 9, 97, 11, 12, 13, 98], ![67, 68, 69, 99, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 100], ![82, 83, 84, 101, 86, 87, 88, 89, 90, 91, 92, 93, 12, 94, 95], ![0, 1, 2, 101, 102, 63, 6, 7, 64, 9, 97, 11, 12, 13, 103], ![104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118], ![67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81], ![119, 120, 121, 122, 86, 123, 124, 125, 90, 126, 127, 93, 12, 94, 95]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixDoubleAllGroup04Data.Mask949

namespace Jsp404.SixDoubleAllGroup04Data.Mask951
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![true, true, true, false, true, true, false, true, true, true]

def rows : RowsData := ![![4, 2, 3, 1], ![4, 2, 3, 0], ![4, 1, 0, 3], ![4, 1, 0, 2], ![3, 2, 1, 0]]

def localCycle000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -1, -3, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-3, -1, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 3 0]

def localCycle003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 1, .triangle 7 0, .triangle 9 1, .gapLower 3 0, .corridorUpper 2 3, .gapLower 2 3]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![0, -3, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 3 0]

def localCycle005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle006 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -1, -2, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .triangle 3 0]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle008 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -2, 2, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 0, .gapLower 2 4, .triangle 3 0]

def localCycle009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 3 0]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![0, -2, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 0 1, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle011 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-2, -1, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle013 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -1, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![0, -3, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3]

def localCycle015 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, 0, -3, -1, 4, -1, -3, -1, 4]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4]

def localCycle016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 3 0]

def localCycle018 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -2, 4, -1, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 3 0, .gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 3 0]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, -2, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3]

def localCycle021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 3 0]

def localCycle022 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, 0, -1, 3, -2, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3, .gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0]

def localCycle024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -1, -3, 4, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle027 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -3, 0, -3, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-3, -1, 0, 0, 4, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .triangle 9 1, .gapLower 3 0, .gapLower 3 4, .gapLower 3 3, .gapLower 0 2]

def localCycle029 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -3, 0, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -1, 0, 1, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, -2, 4, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle032 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, -2, 4, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle033 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -1, -2, 4, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle034 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -1, -2, 2, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle035 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -3, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle036 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -3, 0, -2, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle037 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, 0, -1, 0, 2, 0, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 3 2, .gapLower 0 2]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 0, 0, 4, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .triangle 9 1, .gapLower 3 0, .gapLower 3 4, .gapLower 3 3, .gapLower 0 2]

def localCycle039 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 0, 2, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle040 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -1, -1, 2, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle041 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, -1, -3, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle042 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, -3, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle043 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 3 1, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle044 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 1, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle045 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -1, 1, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0]

def localCycle046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -2, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .triangle 3 1, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle048 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .triangle 3 1, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle050 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, -2, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle051 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, 2, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0]

def localCycle052 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 3 1, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle053 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, 0, -1, -3, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle055 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, 0, -3, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, 0, -3, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, false] }
  origin := ![.triangle 1 2, .triangle 3 1, .gapLower 2 2, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4]

def localCycle057 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, 0, -2, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle058 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, 0, -2, -1, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .triangle 3 1, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, 0, -1, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle060 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, 0, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle061 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![0, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 0 1, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle062 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, 0, -3, -1, 4, -1, -2, -2, 4]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0, .gapLower 0 1, .gapLower 0 0, .gapLower 0 4]

def localCycle063 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 0, 0, 3, -3]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 3]

def localCycle064 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 3 0]

def localCycle065 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 0, 0, 3, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 2 3]

def localCycle066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3]

def localCycle067 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -1, -3, 4, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle068 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -2, 0, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle069 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-3, -1, 0, 0, 4, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .triangle 9 1, .gapLower 3 0, .gapLower 3 4, .gapLower 3 3, .gapLower 0 2]

def localCycle070 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -1, -1, 1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle071 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -2, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle072 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, -2, 4, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle073 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -2, 0, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle074 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-1, -2, 2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle075 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -2, -2, -2, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle076 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -2, 0, -2, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle077 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, -1, 2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle078 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle079 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle080 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -1, 0, -1, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, -1, -3, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle084 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .triangle 3 1, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle086 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0]

def localCycle087 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, -2, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle088 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 0 1, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3]

def localCycle089 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, 0, -3, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle090 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, 0, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle091 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, 0, -1, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle092 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, 0, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3]

def localCycle093 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, 0, -1, 1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle094 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, 0, -1, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 3 3, .gapLower 0 2]

def localCycle095 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0]

def localCycle096 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle097 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![0, 0, -3, -1, 4, -1, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4]

def localCycle098 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, 0, -1, 0, -1, 3, -3, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 7 0, .triangle 9 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4]

def localCycle099 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, 0, -1, -2, 4, -2, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4]

def localCycle100 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, 0, -2, 0, -1, 3, -2, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .corridorUpper 2 3, .gapLower 2 3, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4]

def localCycle101 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 0 1, .triangle 2 1, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 0]

def localCycle102 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .distance 2 3, .distance 0 2, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, 0, -1, -1, 2, -2, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4]

def localCycle103 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -1, -3, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle104 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle105 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle106 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle107 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle108 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -2, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle109 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle110 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle111 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle112 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle113 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, 0, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle114 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, 0, -1, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle115 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle116 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 2, .gapLower 2 2, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4]

def localCycle117 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, 0, 0, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle118 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, 0, 0, -1, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle119 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, 0, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def library : SixWeakOuterReplay.Library
  | 0 => some localCycle000
  | 1 => some localCycle001
  | 2 => some localCycle002
  | 3 => some localCycle003
  | 4 => some localCycle004
  | 5 => some localCycle005
  | 6 => some localCycle006
  | 7 => some localCycle007
  | 8 => some localCycle008
  | 9 => some localCycle009
  | 10 => some localCycle010
  | 11 => some localCycle011
  | 12 => some localCycle012
  | 13 => some localCycle013
  | 14 => some localCycle014
  | 15 => some localCycle015
  | 16 => some localCycle016
  | 17 => some localCycle017
  | 18 => some localCycle018
  | 19 => some localCycle019
  | 20 => some localCycle020
  | 21 => some localCycle021
  | 22 => some localCycle022
  | 23 => some localCycle023
  | 24 => some localCycle024
  | 25 => some localCycle025
  | 26 => some localCycle026
  | 27 => some localCycle027
  | 28 => some localCycle028
  | 29 => some localCycle029
  | 30 => some localCycle030
  | 31 => some localCycle031
  | 32 => some localCycle032
  | 33 => some localCycle033
  | 34 => some localCycle034
  | 35 => some localCycle035
  | 36 => some localCycle036
  | 37 => some localCycle037
  | 38 => some localCycle038
  | 39 => some localCycle039
  | 40 => some localCycle040
  | 41 => some localCycle041
  | 42 => some localCycle042
  | 43 => some localCycle043
  | 44 => some localCycle044
  | 45 => some localCycle045
  | 46 => some localCycle046
  | 47 => some localCycle047
  | 48 => some localCycle048
  | 49 => some localCycle049
  | 50 => some localCycle050
  | 51 => some localCycle051
  | 52 => some localCycle052
  | 53 => some localCycle053
  | 54 => some localCycle054
  | 55 => some localCycle055
  | 56 => some localCycle056
  | 57 => some localCycle057
  | 58 => some localCycle058
  | 59 => some localCycle059
  | 60 => some localCycle060
  | 61 => some localCycle061
  | 62 => some localCycle062
  | 63 => some localCycle063
  | 64 => some localCycle064
  | 65 => some localCycle065
  | 66 => some localCycle066
  | 67 => some localCycle067
  | 68 => some localCycle068
  | 69 => some localCycle069
  | 70 => some localCycle070
  | 71 => some localCycle071
  | 72 => some localCycle072
  | 73 => some localCycle073
  | 74 => some localCycle074
  | 75 => some localCycle075
  | 76 => some localCycle076
  | 77 => some localCycle077
  | 78 => some localCycle078
  | 79 => some localCycle079
  | 80 => some localCycle080
  | 81 => some localCycle081
  | 82 => some localCycle082
  | 83 => some localCycle083
  | 84 => some localCycle084
  | 85 => some localCycle085
  | 86 => some localCycle086
  | 87 => some localCycle087
  | 88 => some localCycle088
  | 89 => some localCycle089
  | 90 => some localCycle090
  | 91 => some localCycle091
  | 92 => some localCycle092
  | 93 => some localCycle093
  | 94 => some localCycle094
  | 95 => some localCycle095
  | 96 => some localCycle096
  | 97 => some localCycle097
  | 98 => some localCycle098
  | 99 => some localCycle099
  | 100 => some localCycle100
  | 101 => some localCycle101
  | 102 => some localCycle102
  | 103 => some localCycle103
  | 104 => some localCycle104
  | 105 => some localCycle105
  | 106 => some localCycle106
  | 107 => some localCycle107
  | 108 => some localCycle108
  | 109 => some localCycle109
  | 110 => some localCycle110
  | 111 => some localCycle111
  | 112 => some localCycle112
  | 113 => some localCycle113
  | 114 => some localCycle114
  | 115 => some localCycle115
  | 116 => some localCycle116
  | 117 => some localCycle117
  | 118 => some localCycle118
  | 119 => some localCycle119
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 15, 2, 16, 17, 18, 19, 20, 21, 9, 22, 23, 24, 23, 25], ![26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40], ![41, 42, 43, 44, 45, 46, 47, 48, 8, 49, 50, 51, 52, 52, 53], ![54, 55, 56, 44, 45, 57, 58, 59, 8, 9, 60, 11, 12, 13, 61], ![0, 62, 2, 63, 64, 5, 6, 7, 8, 9, 65, 51, 12, 13, 66], ![67, 68, 69, 44, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80], ![81, 82, 2, 44, 45, 83, 84, 85, 8, 86, 87, 51, 12, 13, 88], ![0, 89, 2, 44, 45, 90, 6, 91, 8, 9, 10, 51, 12, 13, 61], ![67, 68, 69, 92, 93, 71, 72, 73, 74, 75, 76, 77, 78, 79, 94], ![81, 82, 2, 92, 95, 83, 84, 85, 8, 86, 87, 51, 12, 13, 96], ![0, 97, 2, 98, 95, 90, 6, 99, 8, 9, 100, 101, 12, 13, 102], ![103, 104, 105, 106, 70, 107, 108, 109, 74, 110, 111, 111, 112, 112, 106], ![67, 68, 69, 44, 70, 113, 72, 114, 74, 75, 115, 77, 116, 79, 80], ![81, 82, 2, 44, 45, 117, 84, 118, 8, 86, 119, 51, 12, 13, 88]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixDoubleAllGroup04Data.Mask951

namespace Jsp404.SixDoubleAllGroup04Data.Mask959
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![true, true, true, true, true, true, false, true, true, true]

def rows : RowsData := ![![4, 3, 2, 1], ![4, 2, 3, 0], ![4, 1, 3, 0], ![4, 1, 2, 0], ![3, 2, 1, 0]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -1, -1, -3, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle001 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -1, -3, -1, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle002 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -3, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .corridorUpper 0 2]

def localCycle003 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 3, .triangle 6 0, .triangle 7 0, .corridorLower 2 4, .corridorUpper 0 2]

def localCycle004 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -1, -2, -2, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4]

def localCycle006 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -2, -1, -2, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle007 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, -1, -1, -2, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -1, -1, -2, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -2, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle011 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -1, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle012 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, -2, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 3, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .corridorUpper 0 2]

def localCycle013 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -2, -1, -1, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4]

def localCycle014 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, -1, -1, -1, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 3, .triangle 6 0, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -1, -1, -3, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -3, 0, -1, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2, .gapLower 3 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -3, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .corridorUpper 0 2]

def localCycle018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -1, -2, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -2, -1, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -1, -1, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -1, -1, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -3, 0, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle024 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -3, 0, -1, -2, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2, .gapLower 3 3, .triangle 6 0, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -1, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -2, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .corridorUpper 0 2]

def localCycle027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle028 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle029 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -1, -3, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle030 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -3, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle031 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle032 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-3, -3, -1, 0, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 7 2, .gapLower 1 0, .gapLower 1 4]

def localCycle033 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![0, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -2, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-3, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 7 2, .gapLower 1 0, .corridorUpper 0 1]

def localCycle037 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![0, -1, -1, -2, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle040 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-3, -2, -2, 0, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .triangle 7 2, .gapLower 1 0, .gapLower 1 4]

def localCycle041 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, -1, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 3 0, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle042 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle043 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -1, -3, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 0, .gapLower 2 2, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4]

def localCycle044 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -3, -1, -1, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .triangle 6 0, .triangle 7 0, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle045 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -1, -2, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 3 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle046 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, -1, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, -2, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .gapLower 2 2, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4]

def localCycle048 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-1, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle049 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, 0, -1, -1, -3, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle050 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, 0, -1, -3, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle051 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, 0, -3, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .corridorUpper 0 2]

def localCycle052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, 0, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle053 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, 0, -1, -2, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4]

def localCycle054 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, 0, -2, -1, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle055 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, 0, -1, -1, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .gapLower 2 4]

def localCycle056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -2, 0, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle057 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, 0, -1, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle058 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, 0, -2, -1, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .triangle 7 0, .corridorLower 2 4, .gapLower 2 4]

def localCycle059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -1, -3, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle060 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle061 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle062 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-2, -3, -1, 0, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 7 2, .gapLower 1 0, .gapLower 1 4]

def localCycle063 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle064 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle065 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle066 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle067 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle068 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle069 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle070 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, -1, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 3 0, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle071 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -1, -2, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 3 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle072 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, -1, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle073 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -1, -1, -3, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 3, .triangle 6 0, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle074 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -1, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle075 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle076 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -1, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 3, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle077 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -2, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .triangle 7 0, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle078 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle079 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle080 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle081 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, 0, -2, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2, .gapLower 3 3, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle082 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, 0, -3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4]

def localCycle083 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, -2, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4]

def localCycle084 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, -1, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .triangle 3 0, .gapLower 2 2, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4]

def library : SixWeakOuterReplay.Library
  | 0 => some localCycle000
  | 1 => some localCycle001
  | 2 => some localCycle002
  | 3 => some localCycle003
  | 4 => some localCycle004
  | 5 => some localCycle005
  | 6 => some localCycle006
  | 7 => some localCycle007
  | 8 => some localCycle008
  | 9 => some localCycle009
  | 10 => some localCycle010
  | 11 => some localCycle011
  | 12 => some localCycle012
  | 13 => some localCycle013
  | 14 => some localCycle014
  | 15 => some localCycle015
  | 16 => some localCycle016
  | 17 => some localCycle017
  | 18 => some localCycle018
  | 19 => some localCycle019
  | 20 => some localCycle020
  | 21 => some localCycle021
  | 22 => some localCycle022
  | 23 => some localCycle023
  | 24 => some localCycle024
  | 25 => some localCycle025
  | 26 => some localCycle026
  | 27 => some localCycle027
  | 28 => some localCycle028
  | 29 => some localCycle029
  | 30 => some localCycle030
  | 31 => some localCycle031
  | 32 => some localCycle032
  | 33 => some localCycle033
  | 34 => some localCycle034
  | 35 => some localCycle035
  | 36 => some localCycle036
  | 37 => some localCycle037
  | 38 => some localCycle038
  | 39 => some localCycle039
  | 40 => some localCycle040
  | 41 => some localCycle041
  | 42 => some localCycle042
  | 43 => some localCycle043
  | 44 => some localCycle044
  | 45 => some localCycle045
  | 46 => some localCycle046
  | 47 => some localCycle047
  | 48 => some localCycle048
  | 49 => some localCycle049
  | 50 => some localCycle050
  | 51 => some localCycle051
  | 52 => some localCycle052
  | 53 => some localCycle053
  | 54 => some localCycle054
  | 55 => some localCycle055
  | 56 => some localCycle056
  | 57 => some localCycle057
  | 58 => some localCycle058
  | 59 => some localCycle059
  | 60 => some localCycle060
  | 61 => some localCycle061
  | 62 => some localCycle062
  | 63 => some localCycle063
  | 64 => some localCycle064
  | 65 => some localCycle065
  | 66 => some localCycle066
  | 67 => some localCycle067
  | 68 => some localCycle068
  | 69 => some localCycle069
  | 70 => some localCycle070
  | 71 => some localCycle071
  | 72 => some localCycle072
  | 73 => some localCycle073
  | 74 => some localCycle074
  | 75 => some localCycle075
  | 76 => some localCycle076
  | 77 => some localCycle077
  | 78 => some localCycle078
  | 79 => some localCycle079
  | 80 => some localCycle080
  | 81 => some localCycle081
  | 82 => some localCycle082
  | 83 => some localCycle083
  | 84 => some localCycle084
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![15, 16, 17, 3, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28], ![29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 36, 39, 40, 41, 42], ![0, 1, 43, 44, 4, 5, 6, 7, 8, 45, 46, 11, 47, 48, 14], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![49, 50, 51, 3, 52, 53, 54, 7, 55, 56, 10, 57, 12, 58, 14], ![59, 60, 61, 62, 4, 63, 64, 65, 37, 66, 67, 68, 69, 70, 42], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 71, 72, 11, 12, 13, 14], ![49, 50, 51, 3, 52, 53, 54, 7, 55, 56, 10, 57, 12, 58, 14], ![59, 60, 61, 62, 4, 63, 64, 65, 37, 66, 67, 68, 69, 70, 42], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 71, 72, 11, 12, 13, 14], ![73, 74, 75, 62, 52, 76, 77, 65, 55, 78, 67, 79, 69, 80, 42], ![49, 50, 51, 3, 52, 53, 54, 7, 55, 81, 10, 57, 12, 58, 14], ![59, 60, 82, 62, 4, 63, 64, 65, 37, 66, 67, 68, 83, 84, 42]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixDoubleAllGroup04Data.Mask959

namespace Jsp404.SixDoubleAllGroup04Data.Mask960
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, false, false, false, true, true, true, true]

def rows : RowsData := ![![1, 2, 3, 4], ![0, 4, 3, 2], ![0, 4, 3, 1], ![0, 4, 2, 1], ![0, 3, 2, 1]]

def localCycle000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-3, 4, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle001 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![0, 3, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle002 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -3, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle003 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -3, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle004 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 1, -1, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2, .triangle 0 1]

def localCycle005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-2, 4, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle006 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-2, 4, -1, -2, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 3, -2, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 2, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle009 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle010 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .triangle 0 1]

def localCycle011 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 2, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .triangle 0 1]

def localCycle012 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 2, -1, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, 0, -3, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, -3, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle017 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -3, -1, -3]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle018 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1, -1, -1, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, 0, -2, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, -2, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle021 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, -1, -3]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, -2, -2, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, 0, -2, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle024 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, 0, -2, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, -2, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-3, 4, -1, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -1, -1, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -1, -3, 0, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -3, -1, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 1, -1, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, -1, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, -1, -2, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 3 1, .gapLower 0 2]

def localCycle033 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, -2, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle034 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 2, -1, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -1, -2, 0, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -2, -1, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -1, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -2, -2, 0, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -1, -2, 0, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle040 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -2, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle041 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-3, 3, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle042 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -3, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle043 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 3, -3, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3]

def localCycle044 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![-1, 0, 0, 1, -1, -1, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3]

def localCycle045 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-2, 3, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle046 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 3, -1, -2, 0, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 4 1, .gapLower 0 3, .triangle 3 1]

def localCycle047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 3, -2, -1, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .triangle 3 1]

def localCycle048 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-2, 2, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle049 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-1, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 6 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

def localCycle050 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 3, -2, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3]

def localCycle051 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 2, -1, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3]

def localCycle052 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 3, -2, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 4 2, .gapLower 0 3]

def localCycle053 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 2, -1, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 3]

def localCycle054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 2, -2, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3]

def localCycle055 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 3, -3, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle057 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 3, -2, -1]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle058 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .triangle 0 1]

def localCycle059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .triangle 0 1]

def localCycle060 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-1, 0, 0, 2, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 2, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle061 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 3, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

def localCycle062 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-1, -2, -1, 2]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 6 0, .gapLower 2 2, .corridorLower 2 4, .gapLower 2 4]

def localCycle063 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![-2, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 3, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4]

def localCycle064 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, -3, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle065 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -3, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle066 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -3, -1, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle067 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 1, -1, -1, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle068 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-2, 3, -1, -2, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .triangle 4 0]

def localCycle069 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle071 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle072 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle073 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle074 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle075 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle076 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-3, 4, -1, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle077 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 3, -1, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -1, -3, 0, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle079 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 3, -3, 0, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .triangle 5 0, .gapLower 0 2]

def localCycle080 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 1, -1, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle081 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, -1, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, -1, -2, 0, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle083 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, -2, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle084 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 2, -1, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 3 1, .gapLower 0 2]

def localCycle085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 3, -1, -2, 0, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle086 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 3, -2, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle087 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -1, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle088 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 3, -2, -2, 0, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle089 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -1, -2, 0, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle090 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -2, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle091 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-3, 4, -1, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle092 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -3, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle093 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .triangle 1 1]

def localCycle094 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 1, -1, -1, 0, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2, .triangle 0 1]

def localCycle095 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 3, -2, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .triangle 3 1]

def localCycle096 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 2, -1, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle097 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle098 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .triangle 1 1]

def localCycle099 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .triangle 0 1]

def localCycle100 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 4 2, .gapLower 0 3, .triangle 1 1]

def localCycle101 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 3, .triangle 1 1]

def localCycle102 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .triangle 1 1]

def localCycle103 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -3, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .triangle 3 1, .triangle 0 1]

def localCycle104 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 1, -1, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2, .triangle 0 1]

def localCycle105 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .triangle 0 1]

def localCycle106 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .triangle 0 1]

def localCycle107 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -2, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .triangle 3 1, .triangle 0 1]

def localCycle108 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle109 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle110 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle111 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -3, 0, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle112 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -3, 0, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 3 2, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle113 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -2, 0, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle114 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle115 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, -2, 0, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle116 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, 0, -3, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle117 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, -3, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle118 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 1, -1, -1, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .triangle 3 1, .gapLower 0 1]

def localCycle119 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -2, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle120 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -2, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle121 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle122 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle123 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, -2, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle124 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -2, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 3, .triangle 3 1, .gapLower 0 1]

def localCycle125 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -1, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .triangle 3 1, .gapLower 0 1]

def localCycle126 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1, -1, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle127 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle128 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle129 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -1, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle130 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -1, -3, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 3, .gapLower 0 2]

def localCycle131 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -3, 0, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle132 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 1, -1, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle133 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, -1, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle134 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, -1, -2, 0, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle135 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, -2, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle136 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -1, -2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 3, .gapLower 0 2]

def localCycle137 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 3, -2, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle138 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -1, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle139 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -2, -2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 2, .gapLower 0 3, .gapLower 0 2]

def localCycle140 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -1, -2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 3, .gapLower 0 2]

def localCycle141 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -2, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle142 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -3, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .triangle 5 0, .gapLower 0 2]

def localCycle143 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -1, -2, 0, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle144 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -2, -2, 0, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 2 2, .gapLower 4 2, .triangle 5 0, .gapLower 0 2]

def localCycle145 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 3, -3, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3]

def localCycle146 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![-1, 0, 0, 1, -1, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3]

def localCycle147 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 3, -2, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3]

def localCycle148 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![-1, 0, 0, 2, -1, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 0, .gapLower 4 1, .gapLower 0 3]

def localCycle149 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 3, -2, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 4 2, .gapLower 0 3]

def localCycle150 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 2, -1, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 3]

def localCycle151 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 2, -2, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .triangle 9 0, .gapLower 4 1, .gapLower 0 3]

def library : SixWeakOuterReplay.Library
  | 0 => some localCycle000
  | 1 => some localCycle001
  | 2 => some localCycle002
  | 3 => some localCycle003
  | 4 => some localCycle004
  | 5 => some localCycle005
  | 6 => some localCycle006
  | 7 => some localCycle007
  | 8 => some localCycle008
  | 9 => some localCycle009
  | 10 => some localCycle010
  | 11 => some localCycle011
  | 12 => some localCycle012
  | 13 => some localCycle013
  | 14 => some localCycle014
  | 15 => some localCycle015
  | 16 => some localCycle016
  | 17 => some localCycle017
  | 18 => some localCycle018
  | 19 => some localCycle019
  | 20 => some localCycle020
  | 21 => some localCycle021
  | 22 => some localCycle022
  | 23 => some localCycle023
  | 24 => some localCycle024
  | 25 => some localCycle025
  | 26 => some localCycle026
  | 27 => some localCycle027
  | 28 => some localCycle028
  | 29 => some localCycle029
  | 30 => some localCycle030
  | 31 => some localCycle031
  | 32 => some localCycle032
  | 33 => some localCycle033
  | 34 => some localCycle034
  | 35 => some localCycle035
  | 36 => some localCycle036
  | 37 => some localCycle037
  | 38 => some localCycle038
  | 39 => some localCycle039
  | 40 => some localCycle040
  | 41 => some localCycle041
  | 42 => some localCycle042
  | 43 => some localCycle043
  | 44 => some localCycle044
  | 45 => some localCycle045
  | 46 => some localCycle046
  | 47 => some localCycle047
  | 48 => some localCycle048
  | 49 => some localCycle049
  | 50 => some localCycle050
  | 51 => some localCycle051
  | 52 => some localCycle052
  | 53 => some localCycle053
  | 54 => some localCycle054
  | 55 => some localCycle055
  | 56 => some localCycle056
  | 57 => some localCycle057
  | 58 => some localCycle058
  | 59 => some localCycle059
  | 60 => some localCycle060
  | 61 => some localCycle061
  | 62 => some localCycle062
  | 63 => some localCycle063
  | 64 => some localCycle064
  | 65 => some localCycle065
  | 66 => some localCycle066
  | 67 => some localCycle067
  | 68 => some localCycle068
  | 69 => some localCycle069
  | 70 => some localCycle070
  | 71 => some localCycle071
  | 72 => some localCycle072
  | 73 => some localCycle073
  | 74 => some localCycle074
  | 75 => some localCycle075
  | 76 => some localCycle076
  | 77 => some localCycle077
  | 78 => some localCycle078
  | 79 => some localCycle079
  | 80 => some localCycle080
  | 81 => some localCycle081
  | 82 => some localCycle082
  | 83 => some localCycle083
  | 84 => some localCycle084
  | 85 => some localCycle085
  | 86 => some localCycle086
  | 87 => some localCycle087
  | 88 => some localCycle088
  | 89 => some localCycle089
  | 90 => some localCycle090
  | 91 => some localCycle091
  | 92 => some localCycle092
  | 93 => some localCycle093
  | 94 => some localCycle094
  | 95 => some localCycle095
  | 96 => some localCycle096
  | 97 => some localCycle097
  | 98 => some localCycle098
  | 99 => some localCycle099
  | 100 => some localCycle100
  | 101 => some localCycle101
  | 102 => some localCycle102
  | 103 => some localCycle103
  | 104 => some localCycle104
  | 105 => some localCycle105
  | 106 => some localCycle106
  | 107 => some localCycle107
  | 108 => some localCycle108
  | 109 => some localCycle109
  | 110 => some localCycle110
  | 111 => some localCycle111
  | 112 => some localCycle112
  | 113 => some localCycle113
  | 114 => some localCycle114
  | 115 => some localCycle115
  | 116 => some localCycle116
  | 117 => some localCycle117
  | 118 => some localCycle118
  | 119 => some localCycle119
  | 120 => some localCycle120
  | 121 => some localCycle121
  | 122 => some localCycle122
  | 123 => some localCycle123
  | 124 => some localCycle124
  | 125 => some localCycle125
  | 126 => some localCycle126
  | 127 => some localCycle127
  | 128 => some localCycle128
  | 129 => some localCycle129
  | 130 => some localCycle130
  | 131 => some localCycle131
  | 132 => some localCycle132
  | 133 => some localCycle133
  | 134 => some localCycle134
  | 135 => some localCycle135
  | 136 => some localCycle136
  | 137 => some localCycle137
  | 138 => some localCycle138
  | 139 => some localCycle139
  | 140 => some localCycle140
  | 141 => some localCycle141
  | 142 => some localCycle142
  | 143 => some localCycle143
  | 144 => some localCycle144
  | 145 => some localCycle145
  | 146 => some localCycle146
  | 147 => some localCycle147
  | 148 => some localCycle148
  | 149 => some localCycle149
  | 150 => some localCycle150
  | 151 => some localCycle151
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 15, 16, 17, 18, 19, 20, 21, 8, 22, 23, 24, 25, 20, 21], ![26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40], ![41, 1, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54], ![0, 1, 42, 55, 56, 5, 6, 57, 8, 58, 59, 60, 61, 62, 63], ![0, 64, 65, 66, 67, 45, 68, 69, 8, 70, 71, 72, 73, 74, 75], ![76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90], ![91, 1, 92, 93, 94, 45, 6, 95, 96, 97, 98, 99, 100, 101, 102], ![0, 1, 92, 103, 104, 5, 6, 57, 8, 105, 106, 99, 107, 108, 109], ![76, 110, 111, 112, 80, 81, 82, 83, 84, 113, 114, 87, 115, 89, 90], ![91, 116, 117, 66, 118, 45, 119, 95, 96, 120, 121, 122, 123, 124, 125], ![0, 116, 117, 66, 126, 127, 119, 57, 8, 120, 121, 122, 123, 128, 129], ![76, 1, 130, 131, 132, 133, 134, 135, 84, 136, 137, 138, 139, 140, 141], ![76, 77, 78, 142, 80, 81, 82, 83, 84, 143, 86, 87, 144, 89, 90], ![91, 1, 42, 145, 146, 45, 6, 95, 96, 49, 147, 148, 149, 150, 151]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixDoubleAllGroup04Data.Mask960

namespace Jsp404.SixDoubleAllGroup04Data.Mask992
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, false, false, true, true, true, true, true]

def rows : RowsData := ![![1, 2, 4, 3], ![0, 4, 3, 2], ![0, 4, 3, 1], ![4, 0, 2, 1], ![3, 0, 2, 1]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-3, 4, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .triangle 4 0]

def localCycle001 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![0, 3, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle002 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-1, -3, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 6 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

def localCycle003 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -3, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle004 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 1, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .triangle 4 0, .gapLower 0 1]

def localCycle005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-2, 4, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle006 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-2, 4, -1, -2, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0]

def localCycle007 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 3, -2, -1]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-2, 2, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .triangle 4 0]

def localCycle009 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle010 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .triangle 0 1]

def localCycle011 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 2, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .triangle 0 1]

def localCycle012 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 2, -1, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, 0, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .triangle 9 2, .triangle 4 0, .gapLower 0 1]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, 0, -3, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, -3, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle018 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -3, -1, -3]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1, 0, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .triangle 4 0, .gapLower 0 1]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, 0, -2, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, -2, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle022 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, -1, -3]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, -2, -2, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, 0, -2, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle025 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, 0, -2, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, -2, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-3, 4, -1, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 4 2, .gapLower 0 2]

def localCycle028 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 3, -1, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 9 2, .triangle 4 2, .gapLower 0 2]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 4, -1, -3, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 4, -3, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 1, -1, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 4 2, .gapLower 0 2]

def localCycle032 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-2, 3, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle033 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, 4, -1, -2, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle034 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, 4, -2, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 9 2, .gapLower 4 2, .gapLower 0 2]

def localCycle035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, 2, -1, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 4 2, .gapLower 0 2]

def localCycle036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 4, -1, -2, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 4, -2, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2]

def localCycle038 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 2, -1, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 4 2, .gapLower 0 2]

def localCycle039 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 4, -2, -2, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle040 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 2, -1, -2, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle041 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 2, -2, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2]

def localCycle042 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![-3, 3, -1, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .triangle 4 1]

def localCycle043 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-3, 0, -1, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 3 2]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-3, 0, -1, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2]

def localCycle045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-3, 0, -1, 0, 1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 6 0, .gapLower 3 2]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![-2, 3, -2, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 4 1]

def localCycle047 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .triangle 0 1]

def localCycle048 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-3, 0, -1, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2]

def localCycle049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-3, 0, -1, 0, 2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 6 0, .gapLower 3 2]

def localCycle050 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-1, -2, -1, 2]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 6 0, .gapLower 2 2, .corridorLower 2 4, .gapLower 2 4]

def localCycle051 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-3, 0, -1, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2]

def localCycle052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-1, -1, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 5 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2]

def localCycle053 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2]
    constant := ![-1, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 6 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4]

def localCycle054 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 4, -2, -1]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle055 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![0, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 2 1]

def localCycle056 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-1, 1, -1, -1, 0, 3, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorLower 0 2, .gapLower 0 4, .triangle 5 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 2, .gapLower 2 1]

def localCycle057 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 1, -1, -1, 0, 2, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .triangle 5 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .triangle 0 1]

def localCycle058 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 3, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

def localCycle059 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-1, -1, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 5 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2]

def localCycle060 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, -3, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle061 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -3, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle062 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -3, -1, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle063 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 1, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle064 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-2, 3, -1, -2, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .triangle 4 0]

def localCycle065 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle066 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle067 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle068 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle069 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle071 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle072 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-3, 3, -1, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 9 2, .gapLower 4 2, .gapLower 0 2]

def localCycle073 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 3, -1, -3, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle074 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 3, -3, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2]

def localCycle075 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 1, -1, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 4 2, .gapLower 0 2]

def localCycle076 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, 4, -1, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle077 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![-2, 4, -2, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2]

def localCycle078 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, 2, -1, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 4 2, .gapLower 0 2]

def localCycle079 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

def localCycle080 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2, .triangle 0 1]

def localCycle081 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .triangle 0 1]

def localCycle082 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 3, -2, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle083 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 2, -1, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle084 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 2, -2, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2]

def localCycle085 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-3, 3, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 9 2, .triangle 4 0]

def localCycle086 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -3, 0, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 4 1, .triangle 0 1]

def localCycle087 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 1, -1, 0, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .triangle 4 1, .triangle 0 1]

def localCycle088 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .triangle 0 1]

def localCycle089 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .triangle 0 1]

def localCycle090 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .triangle 0 1]

def localCycle091 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle092 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, 0, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 4 1, .triangle 0 1]

def localCycle093 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -3, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle094 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 1, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .triangle 4 0, .gapLower 0 1]

def localCycle095 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle096 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, 0, -3, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle097 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, -3, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

def localCycle098 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -3, 0, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2, .gapLower 0 1]

def localCycle099 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

def localCycle100 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

def localCycle101 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, 0, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2, .gapLower 0 1]

def localCycle102 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle103 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, -2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

def localCycle104 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2, .gapLower 0 1]

def localCycle105 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, 0, -3, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle106 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .triangle 4 1, .gapLower 0 1]

def localCycle107 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle108 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -2, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle109 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![-2, 3, -2, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 4 1]

def localCycle110 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -1, -2, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle111 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 9 2, .gapLower 2 1, .gapLower 0 1]

def localCycle112 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, -2, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle113 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 0, .gapLower 0 1]

def localCycle114 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 4 1, .gapLower 0 1]

def localCycle115 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1, 0, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .triangle 4 0, .gapLower 0 1]

def localCycle116 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle117 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![-3, 4, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle118 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 4, -1, -3, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle119 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 3, -3, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle120 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 1, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle121 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![-2, 3, -2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle122 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![-2, 2, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle123 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 4, -1, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 4 2, .gapLower 0 2]

def localCycle124 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 3, -2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle125 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![0, 2, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle126 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 2, -1, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 2]

def localCycle127 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 2, -2, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle128 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 4, -3, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2]

def localCycle129 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 3, -2, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .triangle 5 2, .gapLower 0 2]

def localCycle130 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 4, .distance 0 2]
    constant := ![0, 2, -2, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 2, .triangle 5 2, .gapLower 0 2]

def localCycle131 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-2, 0, -1, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2]

def localCycle132 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-2, 0, -1, 0, 1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 6 0, .gapLower 3 2]

def localCycle133 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-2, 0, -1, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2]

def localCycle134 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .theta 0, .distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2]
    constant := ![-1, 2, -2, 0, -1, 0, 2, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorLower 0 2, .gapLower 0 4, .gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 6 0, .triangle 9 2, .gapLower 2 1]

def localCycle135 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 0 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-2, 0, -1, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2]

def library : SixWeakOuterReplay.Library
  | 0 => some localCycle000
  | 1 => some localCycle001
  | 2 => some localCycle002
  | 3 => some localCycle003
  | 4 => some localCycle004
  | 5 => some localCycle005
  | 6 => some localCycle006
  | 7 => some localCycle007
  | 8 => some localCycle008
  | 9 => some localCycle009
  | 10 => some localCycle010
  | 11 => some localCycle011
  | 12 => some localCycle012
  | 13 => some localCycle013
  | 14 => some localCycle014
  | 15 => some localCycle015
  | 16 => some localCycle016
  | 17 => some localCycle017
  | 18 => some localCycle018
  | 19 => some localCycle019
  | 20 => some localCycle020
  | 21 => some localCycle021
  | 22 => some localCycle022
  | 23 => some localCycle023
  | 24 => some localCycle024
  | 25 => some localCycle025
  | 26 => some localCycle026
  | 27 => some localCycle027
  | 28 => some localCycle028
  | 29 => some localCycle029
  | 30 => some localCycle030
  | 31 => some localCycle031
  | 32 => some localCycle032
  | 33 => some localCycle033
  | 34 => some localCycle034
  | 35 => some localCycle035
  | 36 => some localCycle036
  | 37 => some localCycle037
  | 38 => some localCycle038
  | 39 => some localCycle039
  | 40 => some localCycle040
  | 41 => some localCycle041
  | 42 => some localCycle042
  | 43 => some localCycle043
  | 44 => some localCycle044
  | 45 => some localCycle045
  | 46 => some localCycle046
  | 47 => some localCycle047
  | 48 => some localCycle048
  | 49 => some localCycle049
  | 50 => some localCycle050
  | 51 => some localCycle051
  | 52 => some localCycle052
  | 53 => some localCycle053
  | 54 => some localCycle054
  | 55 => some localCycle055
  | 56 => some localCycle056
  | 57 => some localCycle057
  | 58 => some localCycle058
  | 59 => some localCycle059
  | 60 => some localCycle060
  | 61 => some localCycle061
  | 62 => some localCycle062
  | 63 => some localCycle063
  | 64 => some localCycle064
  | 65 => some localCycle065
  | 66 => some localCycle066
  | 67 => some localCycle067
  | 68 => some localCycle068
  | 69 => some localCycle069
  | 70 => some localCycle070
  | 71 => some localCycle071
  | 72 => some localCycle072
  | 73 => some localCycle073
  | 74 => some localCycle074
  | 75 => some localCycle075
  | 76 => some localCycle076
  | 77 => some localCycle077
  | 78 => some localCycle078
  | 79 => some localCycle079
  | 80 => some localCycle080
  | 81 => some localCycle081
  | 82 => some localCycle082
  | 83 => some localCycle083
  | 84 => some localCycle084
  | 85 => some localCycle085
  | 86 => some localCycle086
  | 87 => some localCycle087
  | 88 => some localCycle088
  | 89 => some localCycle089
  | 90 => some localCycle090
  | 91 => some localCycle091
  | 92 => some localCycle092
  | 93 => some localCycle093
  | 94 => some localCycle094
  | 95 => some localCycle095
  | 96 => some localCycle096
  | 97 => some localCycle097
  | 98 => some localCycle098
  | 99 => some localCycle099
  | 100 => some localCycle100
  | 101 => some localCycle101
  | 102 => some localCycle102
  | 103 => some localCycle103
  | 104 => some localCycle104
  | 105 => some localCycle105
  | 106 => some localCycle106
  | 107 => some localCycle107
  | 108 => some localCycle108
  | 109 => some localCycle109
  | 110 => some localCycle110
  | 111 => some localCycle111
  | 112 => some localCycle112
  | 113 => some localCycle113
  | 114 => some localCycle114
  | 115 => some localCycle115
  | 116 => some localCycle116
  | 117 => some localCycle117
  | 118 => some localCycle118
  | 119 => some localCycle119
  | 120 => some localCycle120
  | 121 => some localCycle121
  | 122 => some localCycle122
  | 123 => some localCycle123
  | 124 => some localCycle124
  | 125 => some localCycle125
  | 126 => some localCycle126
  | 127 => some localCycle127
  | 128 => some localCycle128
  | 129 => some localCycle129
  | 130 => some localCycle130
  | 131 => some localCycle131
  | 132 => some localCycle132
  | 133 => some localCycle133
  | 134 => some localCycle134
  | 135 => some localCycle135
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![15, 16, 17, 18, 19, 20, 21, 22, 8, 23, 24, 25, 26, 21, 22], ![27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41], ![42, 43, 2, 44, 45, 32, 6, 46, 8, 47, 48, 49, 48, 50, 51], ![0, 1, 2, 52, 53, 5, 6, 54, 8, 55, 56, 57, 58, 50, 59], ![0, 60, 61, 62, 63, 32, 64, 65, 8, 66, 67, 68, 69, 70, 71], ![72, 1, 73, 74, 75, 32, 76, 77, 78, 79, 80, 81, 82, 83, 84], ![85, 1, 2, 86, 87, 5, 6, 7, 8, 88, 89, 81, 90, 91, 92], ![0, 1, 2, 93, 94, 5, 6, 54, 8, 88, 89, 81, 90, 91, 95], ![72, 96, 97, 98, 99, 32, 76, 77, 78, 100, 101, 102, 103, 83, 104], ![85, 96, 105, 62, 106, 107, 108, 109, 8, 110, 111, 102, 112, 113, 114], ![0, 96, 105, 62, 115, 107, 108, 7, 8, 110, 111, 102, 112, 113, 116], ![117, 1, 118, 119, 120, 32, 76, 121, 122, 123, 124, 125, 124, 126, 127], ![72, 1, 118, 128, 75, 32, 76, 77, 78, 123, 129, 125, 82, 126, 130], ![85, 1, 2, 131, 132, 5, 6, 7, 8, 55, 133, 134, 58, 50, 135]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixDoubleAllGroup04Data.Mask992

namespace Jsp404.SixDoubleAllGroup04Data.Mask1008
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, false, true, true, true, true, true, true]

def rows : RowsData := ![![1, 4, 2, 3], ![0, 4, 3, 2], ![4, 0, 3, 1], ![4, 0, 2, 1], ![3, 2, 0, 1]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -3, 3, -1, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2]

def localCycle001 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, -1, 3, -1, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .triangle 3 0]

def localCycle002 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, 0, 4, -1, -3]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2]

def localCycle003 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, 0, 3, -3, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle004 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-3, 0, 0, 1, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 3, -1, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 3 0]

def localCycle006 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -2, 4, -1, -2]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2]

def localCycle007 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -2, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -2, 2, -1, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2]

def localCycle009 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -1, 3, -1, -2]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2]

def localCycle010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 0, 3, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 0, 2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 6 0, .triangle 3 0]

def localCycle012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 1]

def localCycle013 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 2, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-3, 0, 0, 2, -2, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, 0, -3, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -3, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle017 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1, -1, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -1, -2, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -2, -1, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle020 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -1, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -2, -2, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle022 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -2, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -3, 4, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 3 0]

def localCycle024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -1, 3, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -1, 1, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .triangle 3 0]

def localCycle027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -2, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 3 0]

def localCycle028 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -2, 3, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -2, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -2, 2, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 3 0]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -1, 3, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2]

def localCycle032 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle033 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -1, 2, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .triangle 3 0]

def localCycle034 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -1, 3, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2]

def localCycle035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -1, 2, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 2 2]

def localCycle036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, -1, 2, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -3, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle038 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-3, -1, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle039 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -1, 3, -1, -3]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2]

def localCycle040 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-1, -1, 3, -3, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle041 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -1, 1, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle042 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -2, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle043 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle044 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, 3, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle045 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, 2, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 3, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle048 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 2, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle049 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-1, -1, 3, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle050 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-1, -1, 2, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle051 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-1, -1, 2, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle052 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -1, 3, -3, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle053 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -1, 1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .triangle 3 0]

def localCycle054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 0, 3, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2]

def localCycle055 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -1, 3, -2, -2]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2]

def localCycle056 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -1, 2, -1, -2]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 2 2]

def localCycle057 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -1, 2, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle058 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -3, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle059 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -3, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle060 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 1, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle061 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle062 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle063 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle064 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle065 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle066 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle067 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -3, 4, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2]

def localCycle068 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -3, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 0 2, .triangle 2 1]

def localCycle069 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -3, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 2, .triangle 2 1]

def localCycle070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 1, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .gapLower 0 2, .triangle 2 1]

def localCycle071 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -2, 4, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2]

def localCycle072 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -2, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle073 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -2, 2, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2]

def localCycle074 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 0 2, .triangle 2 1]

def localCycle075 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 2, .triangle 2 1]

def localCycle076 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .gapLower 0 2, .triangle 2 1]

def localCycle077 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 3, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2]

def localCycle078 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2, .triangle 2 1]

def localCycle079 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2, .triangle 2 1]

def localCycle080 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -3, 4, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle081 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-3, -1, 4, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle082 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-1, -1, 3, -3, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle083 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-1, -1, 1, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle084 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -2, 3, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle085 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, 4, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle086 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, 2, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle087 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, -1, 0, 3, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle088 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 2, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle089 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-1, -1, 3, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle090 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-1, -1, 2, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle091 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -1, -3, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2, .gapLower 0 1]

def localCycle092 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2, .gapLower 0 1]

def localCycle093 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 1, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .triangle 3 0]

def localCycle094 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -1, -2, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2, .gapLower 0 1]

def localCycle095 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -2, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2, .gapLower 0 1]

def localCycle096 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .gapLower 0 2, .gapLower 0 1]

def localCycle097 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -2, -2, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .gapLower 0 2, .gapLower 0 1]

def localCycle098 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 0, 0, 2, -1, -2, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2, .gapLower 0 1]

def localCycle099 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 2, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle100 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -1, -3, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle101 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -3, 0, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 4 2, .gapLower 0 1]

def localCycle102 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 3, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle103 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -2, 0, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 4 2, .gapLower 0 1]

def localCycle104 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle105 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle106 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -1, 3, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle107 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -2, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 4 2, .gapLower 0 1]

def localCycle108 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .triangle 4 2, .gapLower 0 1]

def localCycle109 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, -3, 4, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle110 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 3, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2]

def localCycle111 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, -1, 4, -3, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle112 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, -1, 1, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle113 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, -2, 4, -2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle114 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, -2, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle115 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, -1, 4, -2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle116 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 2, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 2 2]

def localCycle117 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, -1, 2, -2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle118 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def library : SixWeakOuterReplay.Library
  | 0 => some localCycle000
  | 1 => some localCycle001
  | 2 => some localCycle002
  | 3 => some localCycle003
  | 4 => some localCycle004
  | 5 => some localCycle005
  | 6 => some localCycle006
  | 7 => some localCycle007
  | 8 => some localCycle008
  | 9 => some localCycle009
  | 10 => some localCycle010
  | 11 => some localCycle011
  | 12 => some localCycle012
  | 13 => some localCycle013
  | 14 => some localCycle014
  | 15 => some localCycle015
  | 16 => some localCycle016
  | 17 => some localCycle017
  | 18 => some localCycle018
  | 19 => some localCycle019
  | 20 => some localCycle020
  | 21 => some localCycle021
  | 22 => some localCycle022
  | 23 => some localCycle023
  | 24 => some localCycle024
  | 25 => some localCycle025
  | 26 => some localCycle026
  | 27 => some localCycle027
  | 28 => some localCycle028
  | 29 => some localCycle029
  | 30 => some localCycle030
  | 31 => some localCycle031
  | 32 => some localCycle032
  | 33 => some localCycle033
  | 34 => some localCycle034
  | 35 => some localCycle035
  | 36 => some localCycle036
  | 37 => some localCycle037
  | 38 => some localCycle038
  | 39 => some localCycle039
  | 40 => some localCycle040
  | 41 => some localCycle041
  | 42 => some localCycle042
  | 43 => some localCycle043
  | 44 => some localCycle044
  | 45 => some localCycle045
  | 46 => some localCycle046
  | 47 => some localCycle047
  | 48 => some localCycle048
  | 49 => some localCycle049
  | 50 => some localCycle050
  | 51 => some localCycle051
  | 52 => some localCycle052
  | 53 => some localCycle053
  | 54 => some localCycle054
  | 55 => some localCycle055
  | 56 => some localCycle056
  | 57 => some localCycle057
  | 58 => some localCycle058
  | 59 => some localCycle059
  | 60 => some localCycle060
  | 61 => some localCycle061
  | 62 => some localCycle062
  | 63 => some localCycle063
  | 64 => some localCycle064
  | 65 => some localCycle065
  | 66 => some localCycle066
  | 67 => some localCycle067
  | 68 => some localCycle068
  | 69 => some localCycle069
  | 70 => some localCycle070
  | 71 => some localCycle071
  | 72 => some localCycle072
  | 73 => some localCycle073
  | 74 => some localCycle074
  | 75 => some localCycle075
  | 76 => some localCycle076
  | 77 => some localCycle077
  | 78 => some localCycle078
  | 79 => some localCycle079
  | 80 => some localCycle080
  | 81 => some localCycle081
  | 82 => some localCycle082
  | 83 => some localCycle083
  | 84 => some localCycle084
  | 85 => some localCycle085
  | 86 => some localCycle086
  | 87 => some localCycle087
  | 88 => some localCycle088
  | 89 => some localCycle089
  | 90 => some localCycle090
  | 91 => some localCycle091
  | 92 => some localCycle092
  | 93 => some localCycle093
  | 94 => some localCycle094
  | 95 => some localCycle095
  | 96 => some localCycle096
  | 97 => some localCycle097
  | 98 => some localCycle098
  | 99 => some localCycle099
  | 100 => some localCycle100
  | 101 => some localCycle101
  | 102 => some localCycle102
  | 103 => some localCycle103
  | 104 => some localCycle104
  | 105 => some localCycle105
  | 106 => some localCycle106
  | 107 => some localCycle107
  | 108 => some localCycle108
  | 109 => some localCycle109
  | 110 => some localCycle110
  | 111 => some localCycle111
  | 112 => some localCycle112
  | 113 => some localCycle113
  | 114 => some localCycle114
  | 115 => some localCycle115
  | 116 => some localCycle116
  | 117 => some localCycle117
  | 118 => some localCycle118
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 1, 15, 16, 17, 5, 18, 19, 8, 18, 19, 20, 21, 22, 19], ![23, 1, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36], ![37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51], ![0, 1, 39, 52, 53, 5, 6, 7, 8, 54, 10, 11, 55, 56, 57], ![0, 1, 58, 59, 60, 5, 6, 7, 8, 61, 62, 63, 64, 65, 66], ![67, 1, 68, 69, 70, 5, 71, 72, 73, 74, 75, 76, 77, 78, 79], ![80, 81, 39, 82, 83, 84, 6, 85, 86, 9, 87, 88, 89, 56, 90], ![0, 1, 39, 52, 53, 5, 6, 7, 8, 54, 10, 11, 55, 56, 57], ![67, 1, 91, 92, 93, 5, 71, 72, 73, 94, 95, 96, 97, 98, 99], ![80, 81, 100, 101, 83, 84, 6, 85, 86, 9, 102, 88, 103, 104, 90], ![0, 1, 100, 59, 105, 5, 6, 7, 8, 54, 106, 11, 107, 104, 108], ![109, 81, 110, 111, 112, 84, 71, 113, 114, 9, 87, 88, 115, 116, 117], ![67, 1, 110, 118, 93, 5, 71, 72, 73, 9, 106, 11, 77, 116, 99], ![80, 81, 39, 82, 83, 84, 6, 85, 86, 9, 87, 88, 89, 56, 90]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixDoubleAllGroup04Data.Mask1008

namespace Jsp404.SixDoubleAllGroup04Data.Mask1012
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, true, false, true, true, true, true, true, true]

def rows : RowsData := ![![4, 1, 2, 3], ![4, 0, 3, 2], ![4, 0, 3, 1], ![4, 0, 2, 1], ![3, 2, 1, 0]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle001 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-3, -1, 3, -1, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .triangle 3 0]

def localCycle002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 4, -1, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle003 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, 0, 4, -3, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -3, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 0]

def localCycle005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 3, -1, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .triangle 3 0]

def localCycle006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -2, 4, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle007 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -2, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle009 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -1, 3, -1, -2]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2]

def localCycle010 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -1, 3, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 0, 2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 6 0, .triangle 3 0]

def localCycle012 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, -3, 0, 0, 3, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 1]

def localCycle013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, -3, 0, 0, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 2 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![0, -3, 0, 0, 2, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, -1, 4, -1, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, -1, 4, -3, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 4, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .gapLower 0 2]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 4, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, -1, 4, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .gapLower 0 2]

def localCycle026 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle027 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -3, 4, -1, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle029 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .triangle 3 0, .gapLower 0 2]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -3, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle031 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 4, -3, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 1, -1, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .gapLower 0 2]

def localCycle033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 4, -1, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .gapLower 0 2]

def localCycle034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 3, -1, -2, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 3, -2, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 2, -1, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle037 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -2, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 4, -2, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, 2, -1, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .gapLower 0 2]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 4, -2, -2, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 2 2, .gapLower 0 2]

def localCycle041 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, 2, -1, -2, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, 2, -2, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle043 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -3, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle044 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-3, -1, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, 0, 4, -3, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -1, 1, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle048 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -2, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle049 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -2, 4, -1, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle050 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, 3, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle051 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, 2, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle053 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 3, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle054 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 2, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle055 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -1, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle057 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle058 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -1, 3, -3, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle059 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -1, 1, -1, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .triangle 3 0]

def localCycle060 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 0, 3, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2]

def localCycle061 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, 0, -1, 0, 3, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0]

def localCycle062 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 1]

def localCycle063 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle064 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-1, -1, 2, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle065 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle066 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -1, -3, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle067 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 0]

def localCycle068 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 4, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle069 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle071 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 1]

def localCycle072 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle073 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle074 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -3, 4, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle075 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -3, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle076 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, 3, -3, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle077 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, 1, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .gapLower 0 2]

def localCycle078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 3, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle079 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 3, -2, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .gapLower 0 2]

def localCycle084 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .gapLower 0 2]

def localCycle085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle086 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle087 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-3, -1, 4, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle088 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -3, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle089 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle090 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -2, 3, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle091 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, -2, 4, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle092 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, -1, 0, 3, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle093 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 2, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle094 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle095 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle096 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -3, 4, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle097 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -1, -3, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle098 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, -1, 4, -3, -1, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle099 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 1, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle100 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2]
    constant := ![-2, -2, 4, -1, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2]

def localCycle101 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 4, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle102 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 4, -2, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle104 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle105 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -2, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle106 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, -1, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .triangle 3 0, .gapLower 0 2]

def localCycle107 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -2, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .gapLower 0 2]

def localCycle108 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .gapLower 0 2]

def localCycle109 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -2, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def localCycle110 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -1, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle111 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -3, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle112 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 1, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle113 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle114 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 6 0, .gapLower 2 2, .triangle 0 1]

def localCycle115 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .triangle 0 1]

def localCycle116 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle117 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 0 1]

def localCycle118 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -3, 4, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle119 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 4, -3, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle120 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 1, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle121 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -2, 4, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3]

def localCycle122 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 4, -2, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle123 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 2, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 6 0, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle124 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![-2, -1, 3, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3]

def localCycle125 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle126 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .gapLower 0 3, .gapLower 0 2]

def localCycle127 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 4, -3, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 2]

def library : SixWeakOuterReplay.Library
  | 0 => some localCycle000
  | 1 => some localCycle001
  | 2 => some localCycle002
  | 3 => some localCycle003
  | 4 => some localCycle004
  | 5 => some localCycle005
  | 6 => some localCycle006
  | 7 => some localCycle007
  | 8 => some localCycle008
  | 9 => some localCycle009
  | 10 => some localCycle010
  | 11 => some localCycle011
  | 12 => some localCycle012
  | 13 => some localCycle013
  | 14 => some localCycle014
  | 15 => some localCycle015
  | 16 => some localCycle016
  | 17 => some localCycle017
  | 18 => some localCycle018
  | 19 => some localCycle019
  | 20 => some localCycle020
  | 21 => some localCycle021
  | 22 => some localCycle022
  | 23 => some localCycle023
  | 24 => some localCycle024
  | 25 => some localCycle025
  | 26 => some localCycle026
  | 27 => some localCycle027
  | 28 => some localCycle028
  | 29 => some localCycle029
  | 30 => some localCycle030
  | 31 => some localCycle031
  | 32 => some localCycle032
  | 33 => some localCycle033
  | 34 => some localCycle034
  | 35 => some localCycle035
  | 36 => some localCycle036
  | 37 => some localCycle037
  | 38 => some localCycle038
  | 39 => some localCycle039
  | 40 => some localCycle040
  | 41 => some localCycle041
  | 42 => some localCycle042
  | 43 => some localCycle043
  | 44 => some localCycle044
  | 45 => some localCycle045
  | 46 => some localCycle046
  | 47 => some localCycle047
  | 48 => some localCycle048
  | 49 => some localCycle049
  | 50 => some localCycle050
  | 51 => some localCycle051
  | 52 => some localCycle052
  | 53 => some localCycle053
  | 54 => some localCycle054
  | 55 => some localCycle055
  | 56 => some localCycle056
  | 57 => some localCycle057
  | 58 => some localCycle058
  | 59 => some localCycle059
  | 60 => some localCycle060
  | 61 => some localCycle061
  | 62 => some localCycle062
  | 63 => some localCycle063
  | 64 => some localCycle064
  | 65 => some localCycle065
  | 66 => some localCycle066
  | 67 => some localCycle067
  | 68 => some localCycle068
  | 69 => some localCycle069
  | 70 => some localCycle070
  | 71 => some localCycle071
  | 72 => some localCycle072
  | 73 => some localCycle073
  | 74 => some localCycle074
  | 75 => some localCycle075
  | 76 => some localCycle076
  | 77 => some localCycle077
  | 78 => some localCycle078
  | 79 => some localCycle079
  | 80 => some localCycle080
  | 81 => some localCycle081
  | 82 => some localCycle082
  | 83 => some localCycle083
  | 84 => some localCycle084
  | 85 => some localCycle085
  | 86 => some localCycle086
  | 87 => some localCycle087
  | 88 => some localCycle088
  | 89 => some localCycle089
  | 90 => some localCycle090
  | 91 => some localCycle091
  | 92 => some localCycle092
  | 93 => some localCycle093
  | 94 => some localCycle094
  | 95 => some localCycle095
  | 96 => some localCycle096
  | 97 => some localCycle097
  | 98 => some localCycle098
  | 99 => some localCycle099
  | 100 => some localCycle100
  | 101 => some localCycle101
  | 102 => some localCycle102
  | 103 => some localCycle103
  | 104 => some localCycle104
  | 105 => some localCycle105
  | 106 => some localCycle106
  | 107 => some localCycle107
  | 108 => some localCycle108
  | 109 => some localCycle109
  | 110 => some localCycle110
  | 111 => some localCycle111
  | 112 => some localCycle112
  | 113 => some localCycle113
  | 114 => some localCycle114
  | 115 => some localCycle115
  | 116 => some localCycle116
  | 117 => some localCycle117
  | 118 => some localCycle118
  | 119 => some localCycle119
  | 120 => some localCycle120
  | 121 => some localCycle121
  | 122 => some localCycle122
  | 123 => some localCycle123
  | 124 => some localCycle124
  | 125 => some localCycle125
  | 126 => some localCycle126
  | 127 => some localCycle127
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![15, 1, 16, 17, 18, 19, 20, 21, 22, 23, 10, 24, 25, 26, 27], ![28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42], ![43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57], ![0, 1, 45, 58, 59, 5, 6, 7, 8, 60, 61, 11, 62, 63, 64], ![65, 1, 66, 58, 67, 5, 68, 7, 69, 70, 10, 11, 71, 72, 73], ![74, 1, 75, 76, 77, 5, 78, 79, 80, 81, 82, 83, 84, 85, 86], ![0, 87, 45, 88, 89, 90, 6, 91, 8, 9, 92, 93, 94, 63, 95], ![0, 1, 45, 58, 59, 5, 6, 7, 8, 60, 61, 11, 62, 63, 64], ![96, 1, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109], ![65, 87, 110, 111, 112, 90, 68, 91, 69, 9, 92, 93, 113, 114, 115], ![65, 1, 110, 58, 116, 5, 68, 7, 69, 9, 61, 11, 117, 114, 64], ![118, 87, 75, 119, 120, 121, 78, 122, 123, 81, 124, 93, 125, 85, 126], ![74, 1, 75, 127, 77, 5, 78, 79, 80, 81, 82, 83, 84, 85, 86], ![0, 87, 45, 88, 89, 90, 6, 91, 8, 9, 92, 93, 94, 63, 95]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixDoubleAllGroup04Data.Mask1012

namespace Jsp404.SixDoubleAllGroup04Data.Mask1016
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, true, true, true, true, true, true, true]

def rows : RowsData := ![![1, 4, 3, 2], ![0, 4, 3, 2], ![4, 3, 0, 1], ![4, 2, 0, 1], ![3, 2, 0, 1]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -3, 3, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.triangle 3 0, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle001 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -3, -1, 4, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, -1, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -1, -1, 0, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3]

def localCycle004 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 1, -1]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 0]

def localCycle005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -2, -2, 4, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle006 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -2, 3, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.gapLower 2 2, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle007 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -2, 4, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -2, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true] }
  origin := ![.triangle 3 0, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -2, 0, -1, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.triangle 3 0, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3]

def localCycle011 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -1, -1, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -1, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -3, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 2, .triangle 5 2, .gapLower 0 1]

def localCycle016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 1, 0, 0, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .triangle 5 2, .gapLower 0 1]

def localCycle017 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -2, 3, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3]

def localCycle018 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -2, -1, 3, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3]

def localCycle019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .triangle 5 2, .gapLower 0 1]

def localCycle020 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, 0, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 2, .triangle 5 2, .gapLower 0 1]

def localCycle021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -3, 4, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .triangle 4 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -2, 4, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .triangle 4 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -2, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle027 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle028 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .triangle 4 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, 0, -3, 4, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle032 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -3, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle033 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle034 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .corridorLower 2 3, .gapLower 2 4, .triangle 0 2]

def localCycle035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, 0, -2, 4, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 0 3, .triangle 3 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, 0, -2, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3]

def localCycle038 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, 0, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle039 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle040 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2]

def localCycle042 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle043 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .corridorLower 2 3, .gapLower 2 4, .triangle 0 2]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -1, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3]

def localCycle045 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-1, 0, -3, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![0, -3, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-3, 0, -1, 0, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 3 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle048 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -1, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 3 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2]

def localCycle049 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![0, -2, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle050 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle051 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-1, 0, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle053 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-1, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -1, -1, 0, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle055 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -3, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .triangle 5 2, .gapLower 0 1]

def localCycle056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 1, 0, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .triangle 5 2, .gapLower 0 1]

def localCycle057 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .triangle 5 2, .gapLower 0 1]

def localCycle058 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 2, .triangle 5 2, .gapLower 0 1]

def localCycle059 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -3, 4, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle060 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -3, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .gapLower 0 2, .triangle 2 1]

def localCycle061 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle062 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .triangle 4 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle063 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -2, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3]

def localCycle064 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle065 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .gapLower 0 2, .triangle 2 1]

def localCycle066 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 2, .gapLower 0 2, .triangle 2 1]

def localCycle067 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, 0, -3, 4, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle068 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def localCycle069 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle070 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .corridorLower 2 3, .gapLower 2 4, .triangle 0 2]

def localCycle071 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle072 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, 0, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 0 3, .triangle 3 1, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle073 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, 0, -2, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3]

def localCycle074 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, 0, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle075 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -2, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3]

def localCycle076 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle077 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .triangle 5 2, .triangle 2 1]

def localCycle078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle079 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-1, 0, -3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.triangle 3 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle080 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-1, -3, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-3, -1, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle082 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1, -1, -1, 0, 1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .gapLower 0 4, .triangle 3 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle083 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-1, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle084 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1, 0, -2, 2, -1]
    coefficient := ![0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .gapLower 0 4, .triangle 3 0, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle086 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle087 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1, -2, -1, 2, -1]
    coefficient := ![0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .gapLower 0 4, .triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle088 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -2, -1, -1, 0, 2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 0, .gapLower 0 4, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle089 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -3, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 3 2, .gapLower 0 2, .gapLower 0 1]

def localCycle090 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle091 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![0, 0, 0, 3, -2, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .gapLower 0 2, .gapLower 0 1]

def localCycle092 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2, .gapLower 0 1]

def localCycle093 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle094 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![0, 4, -3, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 0 3, .triangle 5 2, .gapLower 0 1]

def localCycle095 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 1, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 5 2, .gapLower 0 1]

def localCycle096 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![0, 0, 0, 3, -2, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .triangle 5 2, .gapLower 0 1]

def localCycle097 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 5 2, .gapLower 0 1]

def localCycle098 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .triangle 5 2, .gapLower 0 1]

def localCycle099 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![0, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle100 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, -1, 3, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def localCycle101 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 1]
    constant := ![-1, 2, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .triangle 3 2, .triangle 5 2, .gapLower 0 1]

def localCycle102 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -1, 3, -2]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle103 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -3, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle104 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def localCycle105 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 4, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle106 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle107 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle108 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -2, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .triangle 4 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3]

def localCycle109 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle110 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle111 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle112 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .triangle 4 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle113 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![0, -2, 0, -3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle114 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3]

def localCycle115 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .distance 0 2]
    constant := ![0, -2, -1, 2]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .corridorLower 0 4, .gapLower 0 4]

def localCycle116 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![0, -2, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle117 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 2, .gapLower 4 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3]

def localCycle118 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, 0, -3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle119 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 3, .theta 0, .distance 0 2]
    constant := ![-2, -1, 2]
    coefficient := ![0, 0, 1]
    strict := ![false, false, false] }
  origin := ![.gapLower 0 3, .corridorLower 0 3, .gapLower 0 4]

def localCycle120 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -1, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3]

def library : SixWeakOuterReplay.Library
  | 0 => some localCycle000
  | 1 => some localCycle001
  | 2 => some localCycle002
  | 3 => some localCycle003
  | 4 => some localCycle004
  | 5 => some localCycle005
  | 6 => some localCycle006
  | 7 => some localCycle007
  | 8 => some localCycle008
  | 9 => some localCycle009
  | 10 => some localCycle010
  | 11 => some localCycle011
  | 12 => some localCycle012
  | 13 => some localCycle013
  | 14 => some localCycle014
  | 15 => some localCycle015
  | 16 => some localCycle016
  | 17 => some localCycle017
  | 18 => some localCycle018
  | 19 => some localCycle019
  | 20 => some localCycle020
  | 21 => some localCycle021
  | 22 => some localCycle022
  | 23 => some localCycle023
  | 24 => some localCycle024
  | 25 => some localCycle025
  | 26 => some localCycle026
  | 27 => some localCycle027
  | 28 => some localCycle028
  | 29 => some localCycle029
  | 30 => some localCycle030
  | 31 => some localCycle031
  | 32 => some localCycle032
  | 33 => some localCycle033
  | 34 => some localCycle034
  | 35 => some localCycle035
  | 36 => some localCycle036
  | 37 => some localCycle037
  | 38 => some localCycle038
  | 39 => some localCycle039
  | 40 => some localCycle040
  | 41 => some localCycle041
  | 42 => some localCycle042
  | 43 => some localCycle043
  | 44 => some localCycle044
  | 45 => some localCycle045
  | 46 => some localCycle046
  | 47 => some localCycle047
  | 48 => some localCycle048
  | 49 => some localCycle049
  | 50 => some localCycle050
  | 51 => some localCycle051
  | 52 => some localCycle052
  | 53 => some localCycle053
  | 54 => some localCycle054
  | 55 => some localCycle055
  | 56 => some localCycle056
  | 57 => some localCycle057
  | 58 => some localCycle058
  | 59 => some localCycle059
  | 60 => some localCycle060
  | 61 => some localCycle061
  | 62 => some localCycle062
  | 63 => some localCycle063
  | 64 => some localCycle064
  | 65 => some localCycle065
  | 66 => some localCycle066
  | 67 => some localCycle067
  | 68 => some localCycle068
  | 69 => some localCycle069
  | 70 => some localCycle070
  | 71 => some localCycle071
  | 72 => some localCycle072
  | 73 => some localCycle073
  | 74 => some localCycle074
  | 75 => some localCycle075
  | 76 => some localCycle076
  | 77 => some localCycle077
  | 78 => some localCycle078
  | 79 => some localCycle079
  | 80 => some localCycle080
  | 81 => some localCycle081
  | 82 => some localCycle082
  | 83 => some localCycle083
  | 84 => some localCycle084
  | 85 => some localCycle085
  | 86 => some localCycle086
  | 87 => some localCycle087
  | 88 => some localCycle088
  | 89 => some localCycle089
  | 90 => some localCycle090
  | 91 => some localCycle091
  | 92 => some localCycle092
  | 93 => some localCycle093
  | 94 => some localCycle094
  | 95 => some localCycle095
  | 96 => some localCycle096
  | 97 => some localCycle097
  | 98 => some localCycle098
  | 99 => some localCycle099
  | 100 => some localCycle100
  | 101 => some localCycle101
  | 102 => some localCycle102
  | 103 => some localCycle103
  | 104 => some localCycle104
  | 105 => some localCycle105
  | 106 => some localCycle106
  | 107 => some localCycle107
  | 108 => some localCycle108
  | 109 => some localCycle109
  | 110 => some localCycle110
  | 111 => some localCycle111
  | 112 => some localCycle112
  | 113 => some localCycle113
  | 114 => some localCycle114
  | 115 => some localCycle115
  | 116 => some localCycle116
  | 117 => some localCycle117
  | 118 => some localCycle118
  | 119 => some localCycle119
  | 120 => some localCycle120
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 1, 2, 15, 16, 5, 6, 17, 8, 9, 18, 11, 19, 13, 20], ![21, 1, 2, 22, 23, 24, 24, 25, 26, 27, 28, 29, 28, 29, 30], ![31, 32, 2, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44], ![45, 46, 47, 3, 48, 49, 50, 51, 51, 52, 10, 53, 12, 54, 14], ![0, 1, 2, 55, 56, 5, 6, 17, 8, 9, 10, 11, 57, 13, 58], ![59, 1, 2, 60, 61, 5, 62, 63, 64, 9, 10, 11, 65, 13, 66], ![67, 68, 2, 69, 70, 71, 72, 73, 74, 9, 75, 76, 77, 13, 78], ![79, 80, 81, 3, 82, 83, 84, 7, 85, 86, 10, 87, 12, 88, 14], ![59, 1, 2, 89, 61, 5, 90, 63, 64, 9, 18, 11, 91, 92, 93], ![67, 68, 2, 94, 95, 71, 6, 73, 74, 9, 75, 76, 96, 97, 98], ![79, 80, 81, 3, 48, 99, 84, 7, 8, 100, 10, 101, 102, 13, 14], ![103, 68, 104, 105, 106, 71, 107, 108, 109, 9, 75, 76, 110, 111, 112], ![113, 80, 81, 114, 115, 99, 116, 63, 64, 100, 10, 115, 117, 13, 93], ![118, 68, 81, 69, 119, 71, 84, 73, 74, 86, 75, 76, 102, 119, 120]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixDoubleAllGroup04Data.Mask1016

namespace Jsp404.SixDoubleAllGroup04Data.Mask1020
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, true, true, true, true, true, true, true, true]

def rows : RowsData := ![![4, 1, 3, 2], ![4, 0, 3, 2], ![4, 3, 0, 1], ![4, 2, 0, 1], ![3, 2, 1, 0]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle001 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -3, -1, 4, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, -1, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -1, -1, 0, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -3, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 0]

def localCycle005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle006 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 3, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -2, 4, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -2, 0, -1, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.triangle 3 0, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3]

def localCycle011 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -1, -1, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -1, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 3 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, 4, -1, -3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 4, .gapLower 0 4, .triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def localCycle018 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle022 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -2, -1, 3, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, -3, 4, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle027 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 3, 0, 0, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, 0, 4, -3, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle029 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 1, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -2, 4, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle031 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, -2, 3, -2, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, -2, 2, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 2, 0, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -3, 4, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle037 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -3, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle038 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 3, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 4, -3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 1, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle041 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, -2, 4, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -2, 4, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle043 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -2, 3, -2, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -2, 2, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle045 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3]

def localCycle047 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2]

def localCycle048 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 2, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle050 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle051 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![0, -3, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle052 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-3, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle053 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle054 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-1, -2, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle055 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle057 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, 0, 1, -1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 1 4, .thetaOrder 0, .gapLower 0 4, .triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle058 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -1, -1, 0, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle059 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle060 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 4, -1, -3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .gapLower 0 4, .triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle061 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle062 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 0]

def localCycle063 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -2, -2, 4, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.triangle 3 0, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle064 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle065 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle067 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, -1, 3, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def localCycle068 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle069 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 0]

def localCycle070 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle071 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, -3, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle072 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 3, -3, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle073 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 1, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle074 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -2, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle075 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, -2, 3, -2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle076 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, -2, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle077 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle079 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle081 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def localCycle082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 3, -3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle084 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -2, 4, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle086 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -2, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3]

def localCycle087 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle088 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle089 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .triangle 9 1, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle090 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle091 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-1, -3, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle092 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-3, -1, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle093 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-1, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle094 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle095 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -2, 0, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle096 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 2, -1, -2, -1, 2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0, .gapLower 0 4, .triangle 3 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle097 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 2, -2, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 2, .gapLower 0 0, .gapLower 0 4, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle098 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -3, 4, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle099 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -1, 3, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle100 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, 4, -3, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle101 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -1, 1, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle102 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -2, 3, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -2, 4, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle104 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -2, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle105 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, 4, -2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle106 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .triangle 3 2, .gapLower 0 2]

def localCycle107 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 2, .gapLower 0 2]

def localCycle108 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -1, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle109 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, 4, -3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle110 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -1, 1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle111 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -2, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle112 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -2, 4, -2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle113 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, 4, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle114 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 1 1]

def localCycle115 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .triangle 1 1]

def localCycle116 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, 0, -3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 4, .gapLower 0 4, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle117 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -3, -1, -1, 0, 3, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 4, .gapLower 0 4, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle118 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle119 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle120 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -1, -2, -2, 4, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 4, .gapLower 0 4, .triangle 3 0, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle121 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -2, -2, -1, 4, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 4, .gapLower 0 4, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle122 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 0 1, .triangle 2 1, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle123 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -1, 3, -2]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle124 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -2, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 4, .gapLower 0 4, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle125 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle126 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, -3, 4, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .gapLower 0 2]

def localCycle127 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 3, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3, .gapLower 0 2]

def localCycle128 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, 0, 4, -3, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .gapLower 0 2]

def localCycle129 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .gapLower 0 2]

def localCycle130 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, -2, 3, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3, .gapLower 0 2]

def localCycle131 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -2, 4, -2, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .gapLower 0 2]

def localCycle132 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![0, 0, -2, 2, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .gapLower 0 2]

def localCycle133 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .gapLower 0 2]

def localCycle134 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 2, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .gapLower 0 2]

def localCycle135 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .gapLower 0 2]

def localCycle136 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .gapLower 0 2]

def localCycle137 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -2, 0, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, true, false, true, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .triangle 3 2, .gapLower 0 2]

def localCycle138 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 2, 0, -2]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .triangle 3 2, .gapLower 0 2]

def localCycle139 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle140 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.triangle 2 0, .triangle 7 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3, .triangle 1 1]

def localCycle141 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def library : SixWeakOuterReplay.Library
  | 0 => some localCycle000
  | 1 => some localCycle001
  | 2 => some localCycle002
  | 3 => some localCycle003
  | 4 => some localCycle004
  | 5 => some localCycle005
  | 6 => some localCycle006
  | 7 => some localCycle007
  | 8 => some localCycle008
  | 9 => some localCycle009
  | 10 => some localCycle010
  | 11 => some localCycle011
  | 12 => some localCycle012
  | 13 => some localCycle013
  | 14 => some localCycle014
  | 15 => some localCycle015
  | 16 => some localCycle016
  | 17 => some localCycle017
  | 18 => some localCycle018
  | 19 => some localCycle019
  | 20 => some localCycle020
  | 21 => some localCycle021
  | 22 => some localCycle022
  | 23 => some localCycle023
  | 24 => some localCycle024
  | 25 => some localCycle025
  | 26 => some localCycle026
  | 27 => some localCycle027
  | 28 => some localCycle028
  | 29 => some localCycle029
  | 30 => some localCycle030
  | 31 => some localCycle031
  | 32 => some localCycle032
  | 33 => some localCycle033
  | 34 => some localCycle034
  | 35 => some localCycle035
  | 36 => some localCycle036
  | 37 => some localCycle037
  | 38 => some localCycle038
  | 39 => some localCycle039
  | 40 => some localCycle040
  | 41 => some localCycle041
  | 42 => some localCycle042
  | 43 => some localCycle043
  | 44 => some localCycle044
  | 45 => some localCycle045
  | 46 => some localCycle046
  | 47 => some localCycle047
  | 48 => some localCycle048
  | 49 => some localCycle049
  | 50 => some localCycle050
  | 51 => some localCycle051
  | 52 => some localCycle052
  | 53 => some localCycle053
  | 54 => some localCycle054
  | 55 => some localCycle055
  | 56 => some localCycle056
  | 57 => some localCycle057
  | 58 => some localCycle058
  | 59 => some localCycle059
  | 60 => some localCycle060
  | 61 => some localCycle061
  | 62 => some localCycle062
  | 63 => some localCycle063
  | 64 => some localCycle064
  | 65 => some localCycle065
  | 66 => some localCycle066
  | 67 => some localCycle067
  | 68 => some localCycle068
  | 69 => some localCycle069
  | 70 => some localCycle070
  | 71 => some localCycle071
  | 72 => some localCycle072
  | 73 => some localCycle073
  | 74 => some localCycle074
  | 75 => some localCycle075
  | 76 => some localCycle076
  | 77 => some localCycle077
  | 78 => some localCycle078
  | 79 => some localCycle079
  | 80 => some localCycle080
  | 81 => some localCycle081
  | 82 => some localCycle082
  | 83 => some localCycle083
  | 84 => some localCycle084
  | 85 => some localCycle085
  | 86 => some localCycle086
  | 87 => some localCycle087
  | 88 => some localCycle088
  | 89 => some localCycle089
  | 90 => some localCycle090
  | 91 => some localCycle091
  | 92 => some localCycle092
  | 93 => some localCycle093
  | 94 => some localCycle094
  | 95 => some localCycle095
  | 96 => some localCycle096
  | 97 => some localCycle097
  | 98 => some localCycle098
  | 99 => some localCycle099
  | 100 => some localCycle100
  | 101 => some localCycle101
  | 102 => some localCycle102
  | 103 => some localCycle103
  | 104 => some localCycle104
  | 105 => some localCycle105
  | 106 => some localCycle106
  | 107 => some localCycle107
  | 108 => some localCycle108
  | 109 => some localCycle109
  | 110 => some localCycle110
  | 111 => some localCycle111
  | 112 => some localCycle112
  | 113 => some localCycle113
  | 114 => some localCycle114
  | 115 => some localCycle115
  | 116 => some localCycle116
  | 117 => some localCycle117
  | 118 => some localCycle118
  | 119 => some localCycle119
  | 120 => some localCycle120
  | 121 => some localCycle121
  | 122 => some localCycle122
  | 123 => some localCycle123
  | 124 => some localCycle124
  | 125 => some localCycle125
  | 126 => some localCycle126
  | 127 => some localCycle127
  | 128 => some localCycle128
  | 129 => some localCycle129
  | 130 => some localCycle130
  | 131 => some localCycle131
  | 132 => some localCycle132
  | 133 => some localCycle133
  | 134 => some localCycle134
  | 135 => some localCycle135
  | 136 => some localCycle136
  | 137 => some localCycle137
  | 138 => some localCycle138
  | 139 => some localCycle139
  | 140 => some localCycle140
  | 141 => some localCycle141
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![15, 16, 17, 18, 19, 20, 20, 20, 21, 17, 22, 23, 24, 23, 25], ![26, 1, 27, 28, 29, 30, 30, 31, 32, 27, 33, 34, 33, 34, 35], ![36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50], ![0, 51, 52, 3, 53, 54, 55, 7, 8, 56, 10, 57, 12, 58, 14], ![59, 60, 2, 61, 62, 63, 64, 65, 66, 67, 10, 11, 68, 69, 70], ![71, 1, 2, 72, 73, 63, 74, 75, 76, 9, 22, 77, 78, 79, 80], ![0, 81, 2, 82, 83, 84, 85, 6, 8, 9, 86, 87, 88, 89, 90], ![0, 91, 92, 3, 53, 93, 94, 7, 8, 95, 10, 96, 12, 97, 14], ![98, 1, 99, 100, 101, 5, 102, 103, 104, 67, 22, 11, 105, 106, 107], ![59, 81, 108, 109, 110, 84, 111, 112, 66, 67, 86, 87, 113, 114, 115], ![59, 116, 117, 118, 119, 120, 64, 65, 66, 121, 10, 122, 123, 124, 125], ![126, 81, 127, 128, 129, 84, 130, 131, 132, 127, 133, 134, 135, 134, 136], ![71, 91, 92, 72, 73, 93, 137, 75, 76, 67, 22, 138, 78, 79, 80], ![0, 81, 92, 82, 83, 139, 140, 6, 8, 141, 86, 87, 88, 89, 90]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixDoubleAllGroup04Data.Mask1020

namespace Jsp404.SixDoubleAllGroup04Data.Mask1022
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, true, true, true, true, true, true, true, true, true]

def rows : RowsData := ![![4, 3, 1, 2], ![4, 3, 0, 2], ![4, 3, 0, 1], ![4, 2, 1, 0], ![3, 2, 1, 0]]

def localCycle000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -3, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, -1, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle004 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -3, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 0]

def localCycle005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle006 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 4, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def localCycle011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -1, -1, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3]

def localCycle013 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle015 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -3, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -3, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def localCycle017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -3, 0, -1, 4, -3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .triangle 0 1]

def localCycle018 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -3, 0, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle019 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -3, 0, 0, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -3, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -3, 0, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .triangle 0 0]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -3, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -3, 0, -1, 4, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .triangle 0 1]

def localCycle024 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -3, 0, 0, -1, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -3, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def localCycle027 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle028 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 0, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle029 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, -2, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle031 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 0, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle033 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 0, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle036 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, -1, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle037 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle038 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, -1, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, -3, 4, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -3, -1, 3, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3]

def localCycle041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 3, 0, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3]

def localCycle042 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, -1, 0, 3, -3, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3]

def localCycle043 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 0, 1, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, -2, 3, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3]

def localCycle045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 4, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, -2, 3, -2, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3]

def localCycle047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, -2, 2, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle048 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 0, -1, 0, 3, 0, -3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3]

def localCycle049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, -1, 4, -2, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3]

def localCycle050 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, -1, 2, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 3, -2, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3]

def localCycle052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 2, 0, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle053 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 2, -2, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3]

def localCycle054 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-3, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle055 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle057 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle058 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -1, -1, 0, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, -2, 0, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle060 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -2, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 0]

def localCycle061 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle062 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -2, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle063 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -2, 4, -2, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 0 0, .gapLower 0 4, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle064 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, -2, 0, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle065 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -2, 0, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 0]

def localCycle066 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, -2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle067 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle068 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -3, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle069 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -2, 0, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 2, .triangle 5 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle071 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle072 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle073 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle074 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle075 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def localCycle076 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle077 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -2, 0, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 2, .triangle 5 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle078 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle079 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, -1, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, -3, 4, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -3, -1, 4, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle082 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 3, -3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3]

def localCycle083 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 1, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle084 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, -2, 4, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 4, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle086 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, -2, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3]

def localCycle087 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, -2, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle088 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3]

def localCycle089 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, -1, 4, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3]

def localCycle090 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, -1, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle091 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3]

def localCycle092 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle093 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 2, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3]

def localCycle094 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-3, -1, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle095 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle096 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle097 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -2, 2, -2, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 5 2, .gapLower 0 0, .gapLower 0 4, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle098 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle099 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def localCycle100 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, -1, 4, -3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .triangle 0 1]

def localCycle101 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle102 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, -2, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle103 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle104 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle105 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .theta 1, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, -1, 4, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .gapLower 1 4, .gapLower 2 3, .triangle 0 1]

def localCycle106 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle107 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle108 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3]

def localCycle109 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, 0, 0, 0, 3, -3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3]

def localCycle110 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -1, 1, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle111 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -2, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3]

def localCycle112 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -2, 4, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3]

def localCycle113 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -1, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3]

def localCycle114 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -1, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle115 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, 0, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3]

def localCycle116 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, 2, -3, -1, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle117 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle118 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle119 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, 2, -2, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle120 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -1, 3, -2]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle121 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, 2, -2, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle122 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, -2, 0, 0, -1, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .triangle 0 1]

def localCycle123 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, -3, 4, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle124 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -3, -1, 4, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle125 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, 3, -3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3]

def localCycle126 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, -1, 0, 1, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle127 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, -2, 4, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle128 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3]

def localCycle129 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, 4, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3]

def localCycle130 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle131 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3]

def localCycle132 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, -1, 4, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3]

def localCycle133 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, -1, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle134 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 0, 0, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3]

def localCycle135 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, -1, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3]

def localCycle136 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, -1, 0, 2, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3]

def localCycle137 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -3, -1, -1, 0, 3, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .corridorLower 0 3, .gapLower 0 4, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle138 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, -1, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 0 1]

def localCycle139 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -2, 0, -2, 4, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .corridorLower 0 3, .gapLower 0 4, .gapLower 2 2, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle140 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 3, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -2, -2, -1, 3, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .corridorLower 0 3, .gapLower 0 4, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def localCycle141 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -2, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .corridorLower 0 3, .gapLower 0 4, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 0 0]

def localCycle142 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3]

def library : SixWeakOuterReplay.Library
  | 0 => some localCycle000
  | 1 => some localCycle001
  | 2 => some localCycle002
  | 3 => some localCycle003
  | 4 => some localCycle004
  | 5 => some localCycle005
  | 6 => some localCycle006
  | 7 => some localCycle007
  | 8 => some localCycle008
  | 9 => some localCycle009
  | 10 => some localCycle010
  | 11 => some localCycle011
  | 12 => some localCycle012
  | 13 => some localCycle013
  | 14 => some localCycle014
  | 15 => some localCycle015
  | 16 => some localCycle016
  | 17 => some localCycle017
  | 18 => some localCycle018
  | 19 => some localCycle019
  | 20 => some localCycle020
  | 21 => some localCycle021
  | 22 => some localCycle022
  | 23 => some localCycle023
  | 24 => some localCycle024
  | 25 => some localCycle025
  | 26 => some localCycle026
  | 27 => some localCycle027
  | 28 => some localCycle028
  | 29 => some localCycle029
  | 30 => some localCycle030
  | 31 => some localCycle031
  | 32 => some localCycle032
  | 33 => some localCycle033
  | 34 => some localCycle034
  | 35 => some localCycle035
  | 36 => some localCycle036
  | 37 => some localCycle037
  | 38 => some localCycle038
  | 39 => some localCycle039
  | 40 => some localCycle040
  | 41 => some localCycle041
  | 42 => some localCycle042
  | 43 => some localCycle043
  | 44 => some localCycle044
  | 45 => some localCycle045
  | 46 => some localCycle046
  | 47 => some localCycle047
  | 48 => some localCycle048
  | 49 => some localCycle049
  | 50 => some localCycle050
  | 51 => some localCycle051
  | 52 => some localCycle052
  | 53 => some localCycle053
  | 54 => some localCycle054
  | 55 => some localCycle055
  | 56 => some localCycle056
  | 57 => some localCycle057
  | 58 => some localCycle058
  | 59 => some localCycle059
  | 60 => some localCycle060
  | 61 => some localCycle061
  | 62 => some localCycle062
  | 63 => some localCycle063
  | 64 => some localCycle064
  | 65 => some localCycle065
  | 66 => some localCycle066
  | 67 => some localCycle067
  | 68 => some localCycle068
  | 69 => some localCycle069
  | 70 => some localCycle070
  | 71 => some localCycle071
  | 72 => some localCycle072
  | 73 => some localCycle073
  | 74 => some localCycle074
  | 75 => some localCycle075
  | 76 => some localCycle076
  | 77 => some localCycle077
  | 78 => some localCycle078
  | 79 => some localCycle079
  | 80 => some localCycle080
  | 81 => some localCycle081
  | 82 => some localCycle082
  | 83 => some localCycle083
  | 84 => some localCycle084
  | 85 => some localCycle085
  | 86 => some localCycle086
  | 87 => some localCycle087
  | 88 => some localCycle088
  | 89 => some localCycle089
  | 90 => some localCycle090
  | 91 => some localCycle091
  | 92 => some localCycle092
  | 93 => some localCycle093
  | 94 => some localCycle094
  | 95 => some localCycle095
  | 96 => some localCycle096
  | 97 => some localCycle097
  | 98 => some localCycle098
  | 99 => some localCycle099
  | 100 => some localCycle100
  | 101 => some localCycle101
  | 102 => some localCycle102
  | 103 => some localCycle103
  | 104 => some localCycle104
  | 105 => some localCycle105
  | 106 => some localCycle106
  | 107 => some localCycle107
  | 108 => some localCycle108
  | 109 => some localCycle109
  | 110 => some localCycle110
  | 111 => some localCycle111
  | 112 => some localCycle112
  | 113 => some localCycle113
  | 114 => some localCycle114
  | 115 => some localCycle115
  | 116 => some localCycle116
  | 117 => some localCycle117
  | 118 => some localCycle118
  | 119 => some localCycle119
  | 120 => some localCycle120
  | 121 => some localCycle121
  | 122 => some localCycle122
  | 123 => some localCycle123
  | 124 => some localCycle124
  | 125 => some localCycle125
  | 126 => some localCycle126
  | 127 => some localCycle127
  | 128 => some localCycle128
  | 129 => some localCycle129
  | 130 => some localCycle130
  | 131 => some localCycle131
  | 132 => some localCycle132
  | 133 => some localCycle133
  | 134 => some localCycle134
  | 135 => some localCycle135
  | 136 => some localCycle136
  | 137 => some localCycle137
  | 138 => some localCycle138
  | 139 => some localCycle139
  | 140 => some localCycle140
  | 141 => some localCycle141
  | 142 => some localCycle142
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![15, 1, 16, 17, 18, 5, 19, 19, 20, 21, 10, 22, 23, 22, 24], ![25, 26, 27, 28, 29, 30, 31, 31, 32, 33, 34, 35, 36, 37, 38], ![39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53], ![0, 1, 54, 3, 55, 5, 56, 7, 8, 57, 10, 11, 12, 58, 14], ![0, 1, 2, 59, 60, 5, 61, 62, 8, 63, 10, 11, 64, 65, 66], ![67, 68, 2, 69, 70, 71, 72, 73, 74, 75, 75, 76, 77, 78, 79], ![80, 81, 2, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93], ![0, 1, 94, 3, 55, 5, 95, 7, 8, 96, 10, 11, 12, 97, 14], ![98, 68, 99, 100, 101, 71, 102, 103, 104, 75, 75, 76, 105, 106, 107], ![80, 81, 108, 109, 110, 84, 111, 112, 87, 88, 89, 90, 113, 114, 115], ![0, 1, 116, 117, 118, 5, 61, 62, 8, 119, 10, 11, 120, 121, 122], ![123, 124, 2, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136], ![67, 68, 137, 138, 70, 71, 139, 73, 74, 140, 75, 76, 120, 141, 79], ![80, 81, 94, 82, 83, 84, 142, 86, 87, 88, 89, 90, 91, 92, 93]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixDoubleAllGroup04Data.Mask1022
