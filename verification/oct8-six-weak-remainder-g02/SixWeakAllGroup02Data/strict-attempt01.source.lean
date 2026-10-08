import Jsp000404.SixWeakOuterReplay

/-! SOURCE_ONLY remainder literal words; pure Replay Data, no Catalog import. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Jsp404.SixWeakAllGroup02Data.Mask216
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, true, true, false, true, true, false, false]

def rows : RowsData := ![![1, 3, 4, 2], ![0, 3, 4, 2], ![3, 4, 0, 1], ![2, 0, 1, 4], ![2, 0, 1, 3]]

def localCycle000 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 8 0, .triangle 1 0]

def localCycle001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-3, 0, 0, 0, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 8 0, .gapLower 3 2, .triangle 1 1]

def localCycle002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, 0, 0, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 3, .triangle 1 0]

def localCycle003 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, 0, 0, 2, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 0, .triangle 1 0]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 8 0, .gapLower 1 1]

def localCycle005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -3]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 3, .gapLower 1 1]

def localCycle006 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 0, .gapLower 1 1]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -2, 4, 0, -3, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 3 1, .gapLower 3 0, .gapLower 3 4, .gapLower 4 3, .gapLower 1 2, .triangle 1 2]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![-2, -1, 3, 0, -3, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2, .gapLower 3 2]

def localCycle009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -1, 3, 0, -3, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2, .gapLower 3 2]

def localCycle010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2, .triangle 1 0]

def localCycle011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .gapLower 4 3, .gapLower 1 2, .triangle 1 0]

def localCycle012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4]
    constant := ![0, 0, -2, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, false, false, true] }
  origin := ![.triangle 4 1, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .triangle 2 2]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![-2, -1, 3, -3, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 4 2, .triangle 5 1]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -1, 3, -3, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 8 1, .gapLower 3 2]

def localCycle015 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -3, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .triangle 8 1, .triangle 1 0]

def localCycle016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -2, 0, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.triangle 4 0, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 0 2]

def localCycle017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, 0, -2, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, false, true] }
  origin := ![.triangle 4 2, .triangle 5 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 2]

def localCycle018 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -1, 0, 1, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 7 2, .triangle 8 1, .gapLower 3 2]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.triangle 4 0, .triangle 9 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 2 3]

def localCycle020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 8 0, .gapLower 1 1]

def localCycle021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 8 0, .gapLower 3 2, .triangle 1 1]

def localCycle022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 3, .gapLower 1 1]

def localCycle023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 0, .gapLower 1 1]

def localCycle024 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 4, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 7 2, .gapLower 1 2, .triangle 1 0]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![-2, -1, 3, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2, .gapLower 3 2]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 4, 0, -2, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 7 2, .gapLower 1 2, .gapLower 3 2, .triangle 1 1]

def localCycle027 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 2, .gapLower 1 2, .triangle 1 0]

def localCycle028 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, 4, -2, -1]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![-2, -1, 3, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 4 2, .triangle 5 1]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 8 0, .gapLower 3 2, .triangle 1 1]

def localCycle031 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 4, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .triangle 8 1, .triangle 1 0]

def localCycle032 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle033 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, 0, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 7 2, .triangle 8 1, .gapLower 3 2, .triangle 1 1]

def localCycle034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2, .gapLower 1 1]

def localCycle035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -1, 3, 0, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2, .gapLower 3 2]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .gapLower 4 3, .gapLower 1 2, .gapLower 1 1]

def localCycle037 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .triangle 8 1, .gapLower 1 1]

def localCycle038 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -1, 3, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 8 1, .gapLower 3 2]

def localCycle039 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .gapLower 3 3, .gapLower 1 1]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.triangle 4 0, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 0 2]

def localCycle041 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, 0, -2, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, true, false, true] }
  origin := ![.triangle 4 2, .triangle 5 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 2]

def localCycle042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 7 2, .triangle 8 1, .gapLower 3 2]

def localCycle043 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 0, .gapLower 1 1]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -2, 0, 3, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 3 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2, .gapLower 3 2]

def localCycle045 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![-2, -1, 4, -2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3, .gapLower 1 2, .gapLower 3 2]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -1, 3, -2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2, .gapLower 3 2]

def localCycle047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -1, 3, -2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 2]

def localCycle048 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -2, 0, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true] }
  origin := ![.triangle 3 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 7 2, .gapLower 1 2, .triangle 1 2]

def localCycle049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![-2, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 7 2, .gapLower 1 2, .gapLower 3 2]

def localCycle050 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, 2, 0, -2, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 7 2, .gapLower 1 2, .gapLower 3 2, .triangle 1 1]

def localCycle051 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2]
    constant := ![0, -2, -1, 2]
    coefficient := ![0, 0, 0, 1]
    strict := ![true, false, false, false] }
  origin := ![.triangle 7 2, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 4]

def localCycle052 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .gapLower 4 3, .gapLower 1 2, .triangle 1 0]

def localCycle053 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4]
    constant := ![0, 0, -2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, true, true, false, false, true] }
  origin := ![.triangle 4 1, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .triangle 2 2]

def localCycle054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![-2, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .gapLower 4 2, .triangle 5 1]

def localCycle055 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, -1, 0, 2, -2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .triangle 8 1, .gapLower 3 2]

def localCycle056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 4, .gapLower 1 3, .triangle 2 0]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 0, 1, 2, 3], ![4, 4, 4, 5, 6], ![7, 8, 9, 10, 11], ![12, 13, 14, 15, 15], ![16, 17, 18, 19, 19], ![20, 20, 21, 22, 23], ![24, 25, 26, 24, 27], ![28, 29, 30, 31, 28], ![32, 32, 33, 32, 32], ![34, 25, 35, 34, 36], ![37, 29, 38, 39, 37], ![40, 41, 42, 39, 43], ![44, 45, 46, 47, 47], ![48, 49, 50, 51, 52], ![53, 54, 55, 56, 56]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask216

namespace Jsp404.SixWeakAllGroup02Data.Mask218
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, true, false, true, true, false, true, true, false, false]

def rows : RowsData := ![![3, 1, 4, 2], ![3, 0, 4, 2], ![3, 4, 0, 1], ![2, 1, 0, 4], ![2, 0, 1, 3]]

def localCycle000 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -3, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle001 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -3, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -3, 0, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .gapLower 4 3, .triangle 2 0]

def localCycle003 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle004 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle005 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle006 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-3, 0, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .gapLower 3 4, .gapLower 4 3, .triangle 2 0]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, 4, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 3 0, .gapLower 3 4, .gapLower 4 3, .gapLower 1 2]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 3, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2]

def localCycle009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![0, -2, 0, -1, 3, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -1, 3, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2]

def localCycle011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 3 0, .gapLower 3 4, .gapLower 4 3, .gapLower 1 2]

def localCycle012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![0, 0, -2, 0, 3, -3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .triangle 2 0]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 2 0]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -1, 4, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 1 3, .triangle 2 0]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 2 0]

def localCycle016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle018 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle019 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, 1, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -2, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle021 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle022 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -2, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle023 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle024 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, -2, 0, 0, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 2, .triangle 2 0]

def localCycle025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, 0, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2]

def localCycle027 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -2, 0, 0, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2]

def localCycle028 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, 4, 0, -2]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .gapLower 1 4, .triangle 7 2, .gapLower 1 2]

def localCycle029 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .theta 0, .zero, .theta 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, 0, 0, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 2, .gapLower 1 2]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, 0, 3, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .triangle 2 0]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 2 0]

def localCycle032 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -2, 0, 0, 3, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .triangle 2 0]

def localCycle033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .triangle 2 0]

def localCycle034 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, 2, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle035 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, -2, 0, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2]

def localCycle037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, -2, -1, 4, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 2, .gapLower 1 2]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![0, -2, 0, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2]

def localCycle039 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 2, .gapLower 1 2]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .zero, .theta 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, -1, 0, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .gapLower 4 3, .gapLower 1 2]

def localCycle041 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle042 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle043 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle044 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 2 0]

def localCycle045 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -1, 2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 7 2, .triangle 2 0]

def localCycle048 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, 0, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2]

def localCycle049 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3, .gapLower 1 2]

def localCycle050 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![0, -2, 0, -1, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2]

def localCycle051 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2]

def localCycle052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, 0, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, true, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 7 2, .gapLower 1 2]

def localCycle053 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 7 2, .gapLower 1 2]

def localCycle054 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -1, 2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 7 2, .gapLower 1 2]

def localCycle055 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -1, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 7 2, .gapLower 1 2]

def localCycle056 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .triangle 2 0]

def localCycle057 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -1, 2, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 1 3, .triangle 2 0]

def localCycle058 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-1, -1, 2, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 1 3, .gapLower 1 4, .gapLower 1 3, .triangle 2 0]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 0, 1, 0, 2], ![3, 4, 5, 5, 6], ![7, 8, 9, 10, 11], ![12, 13, 14, 15, 15], ![16, 17, 18, 19, 19], ![20, 21, 22, 23, 24], ![25, 26, 27, 28, 29], ![30, 31, 32, 33, 33], ![34, 34, 35, 34, 34], ![36, 37, 38, 39, 40], ![20, 41, 42, 43, 44], ![45, 46, 47, 45, 45], ![48, 49, 50, 51, 51], ![52, 53, 54, 55, 55], ![30, 56, 57, 58, 58]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask218

namespace Jsp404.SixWeakAllGroup02Data.Mask222
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, true, true, true, true, false, true, true, false, false]

def rows : RowsData := ![![3, 4, 1, 2], ![3, 4, 0, 2], ![3, 4, 0, 1], ![2, 1, 0, 4], ![2, 1, 0, 3]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -2, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle002 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -3, -1, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -3, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle004 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 4 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 0]

def localCycle005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle006 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 4, .triangle 0 0]

def localCycle007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 0, 3, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -2, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .triangle 9 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle011 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -2, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle014 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle015 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -2, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 4 1, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -2, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle020 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -2, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 1, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3]

def localCycle022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -2, -2, 0, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 2, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3]

def localCycle024 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 4, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 1 0, .gapLower 1 4, .gapLower 1 3]

def localCycle025 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -2, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle028 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -2, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3]

def localCycle031 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 4 1, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3]

def localCycle033 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -2, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -2, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 4 1, .triangle 9 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle036 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 4, .triangle 0 0]

def localCycle037 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -2, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle038 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle039 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -2, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3]

def localCycle041 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, 0, -2, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 1 3]

def localCycle042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 7 1, .triangle 9 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 0, 1, 0, 0], ![2, 3, 2, 2, 2], ![4, 5, 6, 6, 6], ![7, 8, 9, 10, 10], ![11, 12, 13, 14, 14], ![15, 16, 15, 15, 15], ![17, 18, 19, 20, 20], ![21, 22, 23, 24, 24], ![25, 25, 26, 25, 25], ![27, 28, 27, 27, 27], ![29, 30, 29, 29, 29], ![31, 31, 31, 31, 31], ![32, 33, 34, 35, 35], ![36, 37, 38, 36, 36], ![39, 40, 41, 42, 42]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask222

namespace Jsp404.SixWeakAllGroup02Data.Mask223
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![true, true, true, true, true, false, true, true, false, false]

def rows : RowsData := ![![3, 4, 2, 1], ![3, 4, 2, 0], ![3, 4, 1, 0], ![2, 1, 0, 4], ![2, 1, 0, 3]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.triangle 0 0, .triangle 7 2, .triangle 8 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![-2, -3, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 2, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 5 0]

def localCycle002 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, 0, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 7 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1]

def localCycle003 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, 0, -3, -1, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 7 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 4]

def localCycle004 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle005 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -3, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle006 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 4]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 4]

def localCycle007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 3, .gapLower 2 2, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle008 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, -1, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 0, .triangle 9 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -1, 0, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, -2, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, 0, -2, -1, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 5 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -1, 0, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .triangle 9 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle014 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -2, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 7 2, .gapLower 1 1, .gapLower 1 0, .gapLower 1 4]

def localCycle015 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, -2, 0, -2, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .triangle 8 1, .gapLower 1 0, .gapLower 1 4]

def localCycle016 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .triangle 8 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 0, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle018 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle019 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 1 3, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3]
    constant := ![-2, -2, 0, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 2, .gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 5 0]

def localCycle020 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 7 2, .triangle 8 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -1, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 7 0, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 4 2, .triangle 5 1, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4]

def localCycle024 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.triangle 0 0, .triangle 7 2, .triangle 8 1, .gapLower 1 0, .gapLower 1 4]

def localCycle025 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1]

def localCycle026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle027 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle028 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 2, .gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle029 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle031 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 7 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 4]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 7 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle033 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapLower 4 1, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle035 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle036 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -2, -1, 2]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 4]

def localCycle037 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, 0, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -1, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 0, .triangle 9 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 2, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle040 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 0, .triangle 9 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 0, 1, 0, 0], ![2, 3, 3, 3, 3], ![4, 5, 6, 6, 6], ![7, 8, 9, 9, 9], ![10, 11, 12, 13, 13], ![14, 14, 14, 14, 14], ![15, 16, 15, 15, 15], ![17, 18, 19, 20, 20], ![21, 22, 23, 24, 24], ![25, 26, 27, 27, 27], ![28, 29, 30, 30, 30], ![31, 32, 31, 31, 31], ![33, 34, 35, 35, 35], ![36, 37, 36, 36, 36], ![38, 39, 40, 40, 40]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask223

namespace Jsp404.SixWeakAllGroup02Data.Mask254
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, true, true, true, true, true, true, true, false, false]

def rows : RowsData := ![![4, 3, 1, 2], ![3, 4, 0, 2], ![3, 4, 0, 1], ![2, 1, 4, 0], ![2, 1, 3, 0]]

def localCycle000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -2, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, 0, -3, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .distance 0 3]
    constant := ![-1, 0, -3, -2, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .gapLower 3 4]

def localCycle005 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, 0, -3, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, -3, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .gapLower 4 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .distance 0 3]
    constant := ![-1, 0, -3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false] }
  origin := ![.triangle 5 0, .triangle 8 2, .gapLower 1 1, .triangle 6 1, .gapLower 3 0, .gapLower 3 4]

def localCycle008 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle011 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 4, .triangle 0 0]

def localCycle012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, 0, 3, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3]

def localCycle013 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -2, -1, 4, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 1 3]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -2, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, 0, -2, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle022 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, 0, -2, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, -2, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .gapLower 4 2, .gapLower 1 1, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -2, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .gapLower 1 3]

def localCycle028 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -2, -2, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4, .gapLower 1 3]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -2, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .gapLower 1 3]

def localCycle030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -2, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle032 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, -2, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle034 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle036 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, -2, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .gapLower 4 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle037 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, 0, -2, 0, -2, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3]

def localCycle038 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, 0, -2, -2, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3]

def localCycle039 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, 0, -2, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle040 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, -2, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .gapLower 4 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle041 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .gapLower 4 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle043 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .distance 0 3]
    constant := ![-1, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .gapLower 3 4]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3]

def localCycle045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3]

def localCycle046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -2, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle048 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle049 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle050 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle051 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle053 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .corridorLower 1 3, .gapLower 1 4, .triangle 0 0]

def localCycle054 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 1 0, .gapLower 1 4, .gapLower 1 3]

def localCycle055 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -2, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3]

def localCycle056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -2, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 1 3]

def localCycle057 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .corridorLower 1 3, .gapLower 1 4, .gapLower 1 3]

def localCycle058 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .triangle 5 0, .triangle 8 0, .corridorLower 1 3, .gapLower 1 4, .gapLower 1 3]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 0, 1, 2, 0], ![3, 4, 5, 6, 7], ![8, 9, 10, 11, 11], ![12, 13, 14, 15, 16], ![17, 18, 19, 20, 17], ![21, 22, 21, 23, 21], ![24, 9, 25, 26, 24], ![27, 27, 28, 29, 27], ![30, 30, 31, 32, 30], ![33, 34, 35, 36, 35], ![37, 38, 39, 40, 39], ![41, 41, 41, 42, 43], ![44, 45, 46, 47, 48], ![49, 50, 51, 52, 53], ![54, 55, 56, 57, 58]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask254

namespace Jsp404.SixWeakAllGroup02Data.Mask255
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![true, true, true, true, true, true, true, true, false, false]

def rows : RowsData := ![![4, 3, 2, 1], ![3, 4, 2, 0], ![3, 4, 1, 0], ![2, 1, 4, 0], ![2, 1, 3, 0]]

def localCycle000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -3, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .triangle 8 0, .gapLower 1 0, .gapLower 1 4]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -2, -3, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4]

def localCycle002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -1, -3, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .triangle 8 0, .gapLower 1 0, .gapLower 1 4]

def localCycle003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 3, .distance 0 3]
    constant := ![-1, -1, -3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 8 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .distance 0 3]
    constant := ![-1, 0, -3, 0, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .gapLower 3 4]

def localCycle005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .distance 0 3]
    constant := ![-1, 0, -3, -2, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .gapLower 3 4]

def localCycle006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 0 2]
    constant := ![0, -1, 0, -3, 0, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4]

def localCycle007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, 0, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .gapLower 4 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .distance 0 3]
    constant := ![-1, 0, -3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .gapLower 3 4]

def localCycle009 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle010 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle011 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 4]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 4]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 0 2]
    constant := ![0, -1, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 5 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 0 2]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, -1, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 0, .triangle 9 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -2, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -2, -1, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -1, -1, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .triangle 8 0, .corridorLower 1 3, .gapLower 1 4]

def localCycle018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .triangle 8 0, .corridorLower 1 3, .gapLower 1 4]

def localCycle019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .theta 2, .distance 0 2]
    constant := ![0, -1, 0, -2, 0, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .gapLower 3 0, .thetaOrder 2, .corridorUpper 0 2]

def localCycle020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .distance 0 2]
    constant := ![0, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4]

def localCycle021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 1 0, .gapLower 1 4]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, 0, -2, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .gapLower 4 2, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 3, .distance 0 3]
    constant := ![-1, 0, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 8 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4]

def localCycle024 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .triangle 8 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .triangle 8 0, .gapLower 1 0, .corridorUpper 0 1]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -2, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .gapLower 3 2, .gapLower 1 0, .corridorUpper 0 1]

def localCycle027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -1, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .triangle 8 0, .gapLower 1 0, .corridorUpper 0 1]

def localCycle028 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .zero, .theta 3, .distance 0 3]
    constant := ![-1, -1, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 8 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .triangle 8 0, .gapLower 1 0, .gapLower 1 4]

def localCycle030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .gapLower 3 2, .gapLower 1 0, .gapLower 1 4]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -1, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .triangle 8 0, .gapLower 1 0, .gapLower 1 4]

def localCycle032 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1]

def localCycle033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle037 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, 0, -2, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .gapLower 4 2, .gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .triangle 8 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 4]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .gapLower 4 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 4]

def localCycle040 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .distance 0 3]
    constant := ![-1, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false] }
  origin := ![.triangle 5 0, .triangle 8 2, .gapLower 1 1, .triangle 6 1, .gapLower 3 0, .gapLower 3 4]

def localCycle041 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle042 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -2, -1, 2]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 4]

def localCycle043 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -1, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle044 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -1, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .triangle 5 0, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4]

def localCycle045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 7 0, .triangle 9 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 0, 1, 2, 3], ![4, 5, 6, 7, 8], ![9, 10, 11, 11, 11], ![12, 10, 13, 13, 13], ![14, 15, 16, 17, 18], ![19, 20, 21, 22, 23], ![24, 25, 26, 27, 24], ![12, 25, 26, 27, 28], ![29, 29, 30, 31, 29], ![32, 33, 34, 34, 34], ![19, 35, 36, 37, 36], ![19, 20, 38, 39, 40], ![41, 10, 41, 41, 41], ![42, 43, 44, 42, 42], ![12, 43, 44, 45, 46]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask255

namespace Jsp404.SixWeakAllGroup02Data.Mask448
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, false, false, false, true, true, true, false]

def rows : RowsData := ![![1, 2, 3, 4], ![0, 4, 3, 2], ![0, 3, 4, 1], ![0, 2, 4, 1], ![0, 2, 3, 1]]

def localCycle000 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 4, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle001 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![-3, 4, 0, -1, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 1, .triangle 1 1]

def localCycle002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 4, 0, -1, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .triangle 3 0, .gapLower 0 1]

def localCycle003 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 4, 0, -2, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle004 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 2, -1, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 8 0, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle005 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![-2, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 9 0, .triangle 3 2]

def localCycle006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, 3, 0, -1, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 1, .triangle 3 1]

def localCycle007 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -1, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .gapLower 3 2, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 3 3, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 2, .gapLower 1 1]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![-2, 4, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .gapLower 3 4, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 1]

def localCycle011 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -3, 0, -1, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 1, .triangle 3 1, .triangle 0 1]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -3, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -3, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle014 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 3 4, .theta 3, .distance 1 3]
    constant := ![-3, 0, -1, 2]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 4 3, .corridorLower 3 4, .gapLower 3 4]

def localCycle015 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![-2, 0, 3, -3, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3, .triangle 9 0, .gapLower 3 1]

def localCycle016 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -3, 0, -1, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3, .triangle 9 0, .gapLower 3 1, .triangle 3 1, .triangle 0 1]

def localCycle017 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 3 3, .gapLower 3 2, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle018 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -3, -2, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .gapLower 4 2, .triangle 4 0, .gapLower 0 1]

def localCycle019 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 3 3, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 1, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![0, 1, 0, -1, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 1, .triangle 1 1]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 1, 0, -1, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .triangle 3 0, .gapLower 0 1]

def localCycle023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 1, 0, -2, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 4, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 4, 0, -1, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 1, .triangle 1 1]

def localCycle026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 4, 0, -1, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .triangle 3 0, .gapLower 0 1]

def localCycle027 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -2, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .gapLower 3 3, .triangle 9 0, .triangle 3 0, .triangle 0 1]

def localCycle028 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 0, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle029 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, 4, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 1 2, .triangle 2 0]

def localCycle030 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 4, 0, -2, 0, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 1, .triangle 1 1]

def localCycle031 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 4, 0, -2, 0, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2, .triangle 3 0, .gapLower 0 1]

def localCycle032 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .triangle 3 0, .triangle 0 1]

def localCycle033 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3, .triangle 9 0, .gapLower 2 1, .gapLower 0 1]

def localCycle034 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -1, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3, .triangle 9 0, .gapLower 3 1, .triangle 3 1, .triangle 0 1]

def localCycle035 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3, .gapLower 3 2, .triangle 3 0, .triangle 0 1]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 4, -2, -2, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .gapLower 4 2, .triangle 4 0, .gapLower 0 1]

def localCycle037 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3, .triangle 9 0, .triangle 3 0, .triangle 0 1]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, 0, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, 0, -1, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 1, .triangle 1 1]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, 0, -1, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .triangle 3 0, .gapLower 0 1]

def localCycle041 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, 0, -2, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle042 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![-2, 4, -2, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .gapLower 3 4, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 1]

def localCycle043 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, 0, -1, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 1, .triangle 3 1, .triangle 0 1]

def localCycle044 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 6 2, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle045 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .gapLower 3 3, .triangle 9 0, .triangle 3 0, .triangle 0 1]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .gapLower 1 2, .gapLower 1 1]

def localCycle047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![-2, 0, 3, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3, .triangle 9 0, .gapLower 3 1]

def localCycle048 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -1, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3, .triangle 9 0, .gapLower 3 1, .triangle 3 1, .triangle 0 1]

def localCycle049 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 3 3, .gapLower 3 2, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle050 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 3 3, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle051 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![-2, 0, 0, 2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 0, .triangle 3 2]

def localCycle053 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![0, 2, 0, -1, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 1, .triangle 1 1]

def localCycle054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, -1, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .triangle 3 0, .gapLower 0 1]

def localCycle055 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2]
    constant := ![0, -2, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 3 3, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 0, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle057 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![-2, 0, 3, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 1]

def localCycle058 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![0, 3, -2, -2, 0, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 2 0, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 1, .triangle 3 1]

def localCycle059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 4, -2, -2, 0, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2, .triangle 3 0, .gapLower 0 1]

def localCycle060 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle061 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 3, .distance 0 1]
    constant := ![0, 2, 0, -2, 0, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 1, .triangle 1 1]

def localCycle062 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, -2, 0, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2, .triangle 3 0, .gapLower 0 1]

def localCycle063 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2]
    constant := ![0, -2, 0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle064 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 2, -2, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .triangle 9 0, .gapLower 2 1, .gapLower 0 1]

def localCycle065 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 3]
    constant := ![-1, 0, 0, 2, -2, 0, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .triangle 9 0, .gapLower 3 1]

def localCycle066 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .gapLower 3 3, .gapLower 3 2, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle067 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 2, -2, -2, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .gapLower 4 2, .triangle 4 0, .gapLower 0 1]

def localCycle068 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .gapLower 3 3, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 1, 2, 3, 4], ![5, 6, 7, 8, 9], ![10, 11, 12, 13, 14], ![15, 16, 17, 18, 19], ![20, 21, 22, 23, 20], ![24, 25, 26, 27, 28], ![29, 30, 31, 27, 32], ![33, 34, 35, 36, 37], ![38, 39, 40, 41, 38], ![42, 43, 44, 45, 46], ![47, 48, 49, 50, 51], ![52, 53, 54, 55, 56], ![57, 58, 59, 50, 60], ![42, 61, 62, 55, 63], ![64, 65, 66, 67, 68]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask448

namespace Jsp404.SixWeakAllGroup02Data.Mask456
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, true, false, false, true, true, true, false]

def rows : RowsData := ![![1, 3, 2, 4], ![0, 4, 3, 2], ![3, 0, 4, 1], ![2, 0, 4, 1], ![0, 2, 3, 1]]

def localCycle000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -2, 0, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.triangle 3 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 9 2, .triangle 4 0]

def localCycle001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![0, -2, -1, 3, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 9 2, .triangle 4 0]

def localCycle002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-3, 4, 0, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .triangle 1 1]

def localCycle003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-3, 4, 0, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .triangle 5 0, .gapLower 0 1]

def localCycle004 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-3, 0, 0, 2, -1, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 8 0, .triangle 9 2, .triangle 4 0, .gapLower 0 2, .gapLower 0 1]

def localCycle005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .gapLower 3 2]

def localCycle006 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![0, -1, 3, 0, -1, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .gapLower 3 2]

def localCycle007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -1, 3, 0, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 3 3, .gapLower 4 2, .triangle 4 0]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 2, .gapLower 1 1]

def localCycle009 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3]
    constant := ![-3, 0, -1, -2, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 0, .gapLower 3 4]

def localCycle010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 3, 0, -3, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 5 0]

def localCycle011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3]
    constant := ![0, -1, 3, 0, -3, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2]

def localCycle012 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -1, 3, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 9 2, .triangle 4 0]

def localCycle013 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3]
    constant := ![-3, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 1, .triangle 9 0, .gapLower 3 0, .gapLower 3 4]

def localCycle014 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 4, -3, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3, .gapLower 3 3, .triangle 5 0]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![0, -1, 3, -3, -1, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 8 0, .gapLower 3 2]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![0, 4, -3, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .triangle 5 0, .gapLower 0 1]

def localCycle018 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle019 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2]
    constant := ![0, -1, -1, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, true, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 0, 1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2]

def localCycle021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![0, 1, 0, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .triangle 1 1]

def localCycle022 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -1, 0, 1, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .gapLower 4 2, .triangle 4 0]

def localCycle023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -1, 0, 1, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 2, .triangle 4 0]

def localCycle024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 4, 0, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .triangle 1 1]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 4, 0, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .triangle 5 0, .gapLower 0 1]

def localCycle026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 2, .gapLower 1 1]

def localCycle027 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2]

def localCycle028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 3, 0, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 5 0]

def localCycle029 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2, .triangle 1 1]

def localCycle030 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, 4, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 1 2, .triangle 2 0]

def localCycle031 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .gapLower 1 2, .triangle 2 0]

def localCycle032 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2]
    constant := ![-2, -1, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 8 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2]

def localCycle033 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 4, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3, .gapLower 3 3, .triangle 5 0]

def localCycle034 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3, .gapLower 3 2, .triangle 1 1]

def localCycle035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 4, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .triangle 5 0, .gapLower 0 1]

def localCycle036 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 4, -2, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .triangle 8 0, .triangle 9 2, .triangle 4 0, .gapLower 0 2, .gapLower 0 1]

def localCycle037 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 2, .triangle 4 0, .gapLower 0 2, .gapLower 0 1]

def localCycle038 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, 0, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .triangle 1 1]

def localCycle039 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, 0, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .triangle 5 0, .gapLower 0 1]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 3, 0, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2]

def localCycle041 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3]
    constant := ![0, -1, 3, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2]

def localCycle042 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .gapLower 1 2, .gapLower 1 1]

def localCycle043 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![0, -1, 3, -2, -1, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 8 0, .gapLower 3 2]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3, .gapLower 4 2, .triangle 4 0]

def localCycle045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -1, 3, -2, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 8 0, .triangle 9 2, .triangle 4 0]

def localCycle046 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -2, 0, 0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false] }
  origin := ![.triangle 3 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 2, .triangle 4 0]

def localCycle047 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![0, -2, -1, 0, 2, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 2, .gapLower 2 2]

def localCycle048 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![0, -1, 0, 2, 0, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2]

def localCycle049 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -1, 0, 2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .gapLower 4 2, .triangle 4 0]

def localCycle050 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -1, 0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .triangle 8 0, .triangle 9 2, .triangle 4 0]

def localCycle051 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2]

def localCycle052 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 4, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3, .gapLower 1 2, .gapLower 4 3, .triangle 5 0]

def localCycle053 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3]
    constant := ![0, -1, 3, -2, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2]

def localCycle054 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -1, 3, -2, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2, .gapLower 4 3, .triangle 9 2, .triangle 4 0]

def localCycle055 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2]
    constant := ![0, -2, 0, -1, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 0, 2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .triangle 5 0]

def localCycle057 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 0 3]
    constant := ![0, -1, 0, 2, 0, -2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, false, false] }
  origin := ![.triangle 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .gapLower 1 2, .gapLower 4 3, .gapLower 3 2]

def localCycle058 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 3, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, 0, 2, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 3 0, .gapLower 3 0, .gapLower 3 4, .gapLower 1 2, .triangle 8 1, .triangle 9 2, .triangle 4 0]

def localCycle059 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2]
    constant := ![-2, -1, -1, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 8 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle060 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .triangle 5 0]

def localCycle061 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![-1, 0, 0, 2, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .gapLower 3 2]

def localCycle062 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![0, 2, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .triangle 5 0, .gapLower 0 1]

def localCycle063 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![-1, -1, 0, 2, -2, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.triangle 3 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .triangle 8 0, .triangle 9 2, .triangle 4 0]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 1, 2, 3, 4], ![0, 5, 6, 7, 8], ![9, 10, 11, 12, 13], ![14, 15, 16, 17, 18], ![19, 20, 21, 22, 23], ![0, 5, 24, 25, 26], ![27, 28, 29, 30, 31], ![32, 33, 34, 35, 36], ![37, 37, 38, 39, 37], ![27, 40, 41, 7, 42], ![32, 33, 43, 44, 45], ![46, 47, 48, 49, 50], ![51, 52, 53, 44, 54], ![55, 56, 57, 49, 58], ![59, 60, 61, 62, 63]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask456

namespace Jsp404.SixWeakAllGroup02Data.Mask504
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, true, true, true, true, true, true, false]

def rows : RowsData := ![![1, 4, 3, 2], ![0, 4, 3, 2], ![3, 4, 0, 1], ![2, 4, 0, 1], ![2, 3, 0, 1]]

def localCycle000 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -1, -1, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 5 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 2]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -1, -2, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 3 2, .triangle 5 0, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def localCycle002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 3 2, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def localCycle003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 3 3]

def localCycle004 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, 0, 2, -1]
    coefficient := ![0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 1 0]

def localCycle005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 2, .gapLower 1 1]

def localCycle006 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -1, -2, 4, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 5 1, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .gapLower 1 2, .gapLower 4 3]

def localCycle007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -2, -1, 3, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 5 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3]

def localCycle008 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -1, -1, 3, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 5 1, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3]

def localCycle009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -1, 0, 2, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 5 1, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .gapLower 1 2, .triangle 2 2]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, 0, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3]

def localCycle011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -2, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-2, -1, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, 0, 4, -3, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .gapLower 1 3, .gapLower 3 3]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3]

def localCycle015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, -1, -1, -2, 0, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, false] }
  origin := ![.triangle 3 2, .triangle 5 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .gapLower 2 3]

def localCycle016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, -1, -2, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 5 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 2]

def localCycle017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, -2, -1, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 2 3]

def localCycle018 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 0, 1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .gapLower 3 3]

def localCycle019 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, -1, -1, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 5 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 2]

def localCycle020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 8 2, .gapLower 1 1]

def localCycle021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -1, -2, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 5 1, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -2, -1, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 5 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 4 3]

def localCycle023 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, 4, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 1 2, .triangle 2 0]

def localCycle024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .gapLower 1 2, .triangle 2 0]

def localCycle025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -2, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3]

def localCycle027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-2, -1, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3]

def localCycle028 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 4, -2, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .triangle 1 1]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 3 3]

def localCycle030 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, -1, -1, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, true, false, false] }
  origin := ![.triangle 3 2, .triangle 5 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .gapLower 2 3]

def localCycle031 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, -1, -2, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 5 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 2 3]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, -2, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 2 3]

def localCycle033 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .triangle 1 1]

def localCycle034 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2, .gapLower 1 1]

def localCycle036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .gapLower 1 2, .gapLower 1 1]

def localCycle037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, 0, 4, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .gapLower 1 3, .gapLower 3 3]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, -1, -2, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 5 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 2]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .gapLower 3 3]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, -1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 5 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 2]

def localCycle041 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -2, -1, 4, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 5 0, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3, .gapLower 3 3]

def localCycle042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -1, -1, 3, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 5 1, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2, .gapLower 4 3]

def localCycle043 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -1, -2, 0, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, false] }
  origin := ![.triangle 5 1, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .gapLower 1 2, .gapLower 4 3]

def localCycle044 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -1, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 5 1, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .gapLower 1 2, .gapLower 4 3]

def localCycle045 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3]

def localCycle046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -2, -1, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 5 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3]

def localCycle047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-2, -1, -1, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3]

def localCycle048 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .gapLower 2 0, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3]

def localCycle049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.triangle 5 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 1, 2, 3, 4], ![0, 1, 2, 3, 5], ![6, 7, 8, 8, 9], ![10, 11, 12, 13, 14], ![15, 16, 17, 18, 19], ![0, 1, 2, 3, 20], ![21, 22, 23, 3, 24], ![25, 26, 27, 28, 29], ![30, 31, 32, 33, 34], ![21, 1, 35, 3, 36], ![25, 26, 27, 37, 29], ![30, 38, 32, 39, 40], ![25, 41, 27, 37, 42], ![43, 31, 32, 39, 44], ![45, 46, 47, 48, 49]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask504

namespace Jsp404.SixWeakAllGroup02Data.Mask508
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, true, true, true, true, true, true, true, false]

def rows : RowsData := ![![4, 1, 3, 2], ![4, 0, 3, 2], ![3, 4, 0, 1], ![2, 4, 0, 1], ![2, 3, 1, 0]]

def localCycle000 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -3, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -3, 4, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .triangle 1 1]

def localCycle002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, -1, -2, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle005 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-3, 0, -1, -1, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 3 3, .triangle 1 1]

def localCycle006 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .triangle 1 0]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, -2, 4, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .gapLower 1 2]

def localCycle008 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, -1, 3, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2]

def localCycle009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, -1, 3, 0, -3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, 0, 2, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .gapLower 1 2]

def localCycle011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, 0, 3, -3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .gapLower 1 3, .triangle 1 0]

def localCycle012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, -1, 3, -3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 1 0]

def localCycle013 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, 0, 4, -3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .gapLower 1 3, .triangle 1 0]

def localCycle014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 0, 4, -3, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .gapLower 1 3, .gapLower 3 3, .triangle 1 1]

def localCycle015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -1, -2, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2]
    constant := ![0, -2, -1, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 2 3]

def localCycle018 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .gapLower 3 3, .triangle 1 1]

def localCycle019 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -1, -2, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .triangle 0 0]

def localCycle021 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, -1, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 3 3, .triangle 1 1]

def localCycle024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .triangle 1 0]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, -2, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .gapLower 1 2]

def localCycle026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2]

def localCycle027 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2]

def localCycle028 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .gapLower 1 2]

def localCycle029 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, -2, 0, 3, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .triangle 1 0]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 1 0]

def localCycle031 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .triangle 1 0]

def localCycle032 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, 4, -2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .triangle 1 1]

def localCycle033 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, 2, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle034 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, -2, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .gapLower 1 2]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -2, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, -1, 3, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .gapLower 1 2]

def localCycle037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 3 0, .gapLower 3 4, .gapLower 1 2]

def localCycle038 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, -2, 0, 3, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .triangle 1 0]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -2, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 1 0]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, -1, -1, 3, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .triangle 1 0]

def localCycle041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, -1, 0, 4, -2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .gapLower 1 3, .gapLower 3 3, .triangle 1 1]

def localCycle042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, -2, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle043 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, 2, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 4, .gapLower 1 4, .triangle 0 0]

def localCycle044 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, -2, 0, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2]

def localCycle045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, -1, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2]

def localCycle046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, -1, 3, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3, .gapLower 1 2]

def localCycle047 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, -1, 0, 4, -2, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .gapLower 1 3, .gapLower 3 3, .triangle 1 1]

def localCycle048 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, -1, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .gapLower 1 2]

def localCycle049 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 6 2, .gapLower 1 2]

def localCycle050 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, -1, 0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .triangle 1 0]

def localCycle051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3, .triangle 1 0]

def localCycle052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 2, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 2, -2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 3, .triangle 1 1]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 0, 0, 1, 0], ![2, 3, 4, 5, 6], ![7, 8, 9, 9, 10], ![11, 12, 13, 14, 13], ![15, 16, 17, 18, 19], ![20, 21, 22, 23, 24], ![25, 26, 27, 27, 28], ![29, 30, 31, 32, 31], ![33, 33, 33, 33, 33], ![34, 35, 36, 36, 37], ![38, 39, 40, 41, 40], ![20, 42, 43, 43, 24], ![44, 45, 46, 47, 46], ![25, 48, 49, 49, 28], ![29, 50, 51, 52, 51]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask508

namespace Jsp404.SixWeakAllGroup02Data.Mask510
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, true, true, true, true, true, true, true, true, false]

def rows : RowsData := ![![4, 3, 1, 2], ![4, 3, 0, 2], ![3, 4, 0, 1], ![2, 4, 1, 0], ![2, 3, 1, 0]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 8 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle003 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -3, 0, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle004 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -3, 0, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle005 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -3, 0, -1, 0, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle006 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -3, 0, -1, 0, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, -2, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, -2, 0, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 4 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, -1, -1, 0, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -1, 0, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .gapLower 1 3]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -2, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -1, 0, 4, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 2, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .gapLower 1 3]

def localCycle014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -1, 0, 4, -3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .gapLower 1 3]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -1, 0, 4, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .gapLower 2 4, .gapLower 1 3]

def localCycle016 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 8 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -2, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle018 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -1, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -1, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle020 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -1, -1, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, 0, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle022 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -2, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -2, -2, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .gapLower 1 1, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 4 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 0]

def localCycle027 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle028 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -1, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .gapLower 1 3]

def localCycle030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -2, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -1, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -1, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle033 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -1, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle034 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 8 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 2, .gapLower 1 0, .gapLower 1 4, .triangle 0 0]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, -1, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle037 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, -2, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle038 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -2, 0, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, -1, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 0]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, 0, -1, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .gapLower 1 3]

def localCycle041 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, 0, -2, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3]

def localCycle042 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -2, 0, -1, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle043 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, 0, -1, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle044 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 4, .triangle 0 0]

def localCycle045 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 4, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 4, .triangle 0 0]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, -1, 0, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2, .gapLower 1 3]

def localCycle047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, -2, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 1 3]

def localCycle048 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 4 1, .corridorLower 2 4, .gapLower 2 4, .gapLower 1 3]

def localCycle049 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, -1, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 3]

def localCycle050 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, -2, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle051 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 2, .gapLower 4 1, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle053 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, -1, -1, -1, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .triangle 0 0]

def localCycle054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -2, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3]

def localCycle055 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -2, -1, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3]

def localCycle056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![0, -2, -1, -1, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 3, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3]

def localCycle057 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-1, -1, -1, -1, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4, .gapLower 1 3]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 1, 0, 2, 0], ![3, 4, 5, 6, 5], ![7, 8, 9, 10, 10], ![11, 12, 13, 14, 15], ![16, 17, 18, 19, 20], ![21, 22, 22, 23, 22], ![24, 25, 26, 27, 28], ![29, 30, 31, 32, 33], ![34, 34, 34, 35, 34], ![36, 37, 26, 38, 39], ![40, 41, 31, 42, 43], ![21, 44, 44, 45, 44], ![46, 47, 48, 32, 49], ![24, 50, 51, 52, 53], ![29, 54, 55, 56, 57]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask510

namespace Jsp404.SixWeakAllGroup02Data.Mask511
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![true, true, true, true, true, true, true, true, true, false]

def rows : RowsData := ![![4, 3, 2, 1], ![4, 3, 2, 0], ![3, 4, 1, 0], ![2, 4, 1, 0], ![2, 3, 1, 0]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .triangle 8 2, .gapLower 1 0, .corridorUpper 0 1]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, 0, -3, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .triangle 8 2, .gapLower 1 0, .gapLower 1 4]

def localCycle002 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, 0, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .gapLower 1 1, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -3, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .gapLower 1 1, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle005 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

def localCycle006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -3, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 3 2, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle007 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle008 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle009 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -2, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle010 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -1, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle012 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -1, -1, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle013 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -1, -2, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle014 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -1, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -1, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle017 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -2, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle018 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -2, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .gapLower 1 1, .gapLower 1 0, .gapLower 1 4]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -2, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle020 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .triangle 8 2, .gapLower 1 0, .corridorUpper 0 1]

def localCycle021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 3 2, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle022 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle026 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -1, -1, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle027 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -1, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .triangle 8 2, .gapLower 1 0, .gapLower 1 4]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle031 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .distance 0 2]
    constant := ![0, -2, -2, 0, -1, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 1, .gapLower 1 2, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .corridorUpper 0 2]

def localCycle032 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 3 2, .gapLower 4 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle034 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle035 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 0, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle036 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle037 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -2, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle038 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 0, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle039 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, 0, -1, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .gapLower 1 1, .gapLower 4 2, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle040 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, 0, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .gapLower 1 1, .gapLower 4 2, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle041 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 6 2, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 4]

def localCycle042 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 1 3, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .gapLower 1 1, .corridorLower 1 4, .gapLower 1 4]

def localCycle043 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, -1, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 8 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapLower 3 2, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -2, 0, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapLower 3 2, .gapLower 4 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle047 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -1, -1, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .triangle 8 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle048 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, 0, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 3 2, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .gapLower 3 2, .gapLower 4 1, .corridorLower 2 4, .thetaOrder 1, .gapLower 1 4]

def localCycle050 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 1 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -1, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle052 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .triangle 8 0, .gapLower 3 1, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle053 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .gapLower 3 2, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle054 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .triangle 3 2, .gapLower 3 3, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

def localCycle055 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .thetaOrder 1, .gapLower 1 4]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 0, 0, 1, 0], ![2, 3, 2, 4, 2], ![5, 6, 5, 5, 5], ![7, 8, 9, 10, 11], ![12, 13, 14, 15, 16], ![17, 17, 18, 19, 18], ![20, 21, 20, 20, 20], ![22, 23, 24, 10, 25], ![26, 27, 28, 29, 30], ![31, 32, 33, 34, 34], ![35, 36, 24, 37, 38], ![39, 40, 41, 42, 41], ![43, 44, 45, 46, 46], ![47, 48, 49, 50, 50], ![51, 52, 53, 54, 55]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask511

namespace Jsp404.SixWeakAllGroup02Data.Mask512
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, false, false, false, false, false, false, true]

def rows : RowsData := ![![1, 2, 3, 4], ![0, 2, 3, 4], ![0, 1, 4, 3], ![0, 1, 4, 2], ![0, 1, 3, 2]]

def localCycle000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 6 0, .triangle 0 0]

def localCycle001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 3 1, .triangle 1 1]

def localCycle002 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 1 0]

def localCycle003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -2, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 2, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 6 0, .triangle 0 0]

def localCycle005 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, 3, -1, -1]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .triangle 5 0]

def localCycle006 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .gapLower 1 1]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 6 0, .gapLower 1 1]

def localCycle008 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -1, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2, .gapLower 1 1]

def localCycle009 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -1, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .gapLower 1 1]

def localCycle010 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle011 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .gapLower 1 2, .triangle 0 0]

def localCycle012 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![-2, 3, -1, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, 3, -1, 0, -3, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1]

def localCycle016 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, 0, -3, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 6 1, .triangle 0 0]

def localCycle017 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -3, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3, .triangle 6 1, .triangle 0 0]

def localCycle018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 1, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![-1, 0, 0, 1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 4, .triangle 8 1, .gapLower 3 1]

def localCycle020 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 6 1, .triangle 0 0]

def localCycle021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .triangle 6 1, .triangle 0 0]

def localCycle022 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .triangle 6 1, .triangle 0 0]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 6 0, .gapLower 1 1]

def localCycle024 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 6 1, .gapLower 1 1]

def localCycle025 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2, .gapLower 1 1]

def localCycle026 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .gapLower 1 1]

def localCycle027 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle028 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .gapLower 1 2, .triangle 0 0]

def localCycle029 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle030 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle031 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, -2, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 6 1, .triangle 0 0]

def localCycle032 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1, .triangle 1 1]

def localCycle033 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 4, -2, -1]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .triangle 1 0]

def localCycle034 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3, .triangle 6 1, .triangle 0 0]

def localCycle035 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, 0, -2, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 6 1, .triangle 0 0]

def localCycle036 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 2 0]

def localCycle037 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .triangle 8 1, .gapLower 3 1, .triangle 1 1]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 1 0]

def localCycle039 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle040 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .gapLower 1 1]

def localCycle042 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .gapLower 1 2, .gapLower 1 1]

def localCycle043 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2, .gapLower 1 1]

def localCycle044 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .gapLower 1 1]

def localCycle045 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1]

def localCycle046 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1, .triangle 3 1, .triangle 0 1]

def localCycle047 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 6 1, .gapLower 1 1]

def localCycle048 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3, .triangle 6 1, .gapLower 1 1]

def localCycle049 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 6 1, .gapLower 1 1]

def localCycle050 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 3 1, .triangle 3 1, .triangle 0 1]

def localCycle051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .triangle 6 1, .gapLower 1 1]

def localCycle052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 6 0, .gapLower 1 1]

def localCycle053 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1]

def localCycle054 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .gapLower 1 2, .triangle 0 0]

def localCycle055 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3, .gapLower 1 2, .triangle 0 0]

def localCycle056 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, 0, -2, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 1 2, .triangle 0 0]

def localCycle057 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![-2, 3, -1, -1, -2, -1, 2, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .corridorLower 1 2, .gapLower 1 4, .triangle 2 2, .triangle 5 1]

def localCycle058 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle060 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2, .triangle 0 0]

def localCycle061 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![0, 2, -2, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 1 3, .gapLower 3 1, .triangle 1 1]

def localCycle062 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 1 0]

def localCycle063 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3, .triangle 6 1, .triangle 0 0]

def localCycle064 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 1, 2, 3, 4], ![5, 6, 7, 8, 9], ![10, 10, 11, 12, 13], ![14, 15, 16, 17, 18], ![5, 19, 20, 21, 22], ![5, 23, 24, 25, 26], ![27, 27, 28, 29, 30], ![31, 32, 33, 34, 35], ![36, 37, 38, 39, 40], ![41, 41, 42, 43, 44], ![45, 46, 47, 48, 49], ![5, 50, 47, 51, 52], ![45, 53, 54, 55, 56], ![57, 58, 54, 59, 60], ![45, 61, 62, 63, 64]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask512

namespace Jsp404.SixWeakAllGroup02Data.Mask513
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![true, false, false, false, false, false, false, false, false, true]

def rows : RowsData := ![![2, 1, 3, 4], ![2, 0, 3, 4], ![1, 0, 4, 3], ![0, 1, 4, 2], ![0, 1, 3, 2]]

def localCycle000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .triangle 1 0]

def localCycle001 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -3, 0, 0, 3, -1, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 3 1, .triangle 1 1]

def localCycle002 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![0, -3, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 1 0]

def localCycle003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -3, 0, 0, 3, -2, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .triangle 1 0]

def localCycle004 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -3, 0, 0, 2, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .triangle 1 0]

def localCycle005 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-3, -1, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .triangle 1 0]

def localCycle006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-3, 0, 4, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .triangle 9 0, .triangle 8 0, .gapLower 3 1, .triangle 1 1]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, 4, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 3 2, .triangle 1 0]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-3, 0, 4, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 4 2, .triangle 2 0]

def localCycle009 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-3, -1, 0, 0, 0, 2, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .triangle 1 0]

def localCycle010 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 0, 0, 0, 3, -1, -1, -3]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2]

def localCycle011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 4, -1, -2, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 0, .gapLower 2 4, .triangle 9 0, .gapLower 3 2, .gapLower 1 2]

def localCycle012 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2]

def localCycle013 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![-2, 3, -1, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, 3, -1, 0, -3, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1]

def localCycle016 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, -1, 0, -3, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

def localCycle017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 4, -2, 0, -3, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

def localCycle018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

def localCycle019 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 4, .triangle 8 1, .triangle 1 0]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, 1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 4, .triangle 8 1, .gapLower 3 1, .triangle 1 1]

def localCycle021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 1 0]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .triangle 1 0]

def localCycle023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .triangle 1 0]

def localCycle024 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -1, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 3 1, .triangle 1 1]

def localCycle025 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 1 0]

def localCycle026 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -2, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .triangle 1 0]

def localCycle027 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, -2, 0, 0, 0, 2, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .triangle 1 0]

def localCycle028 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2]

def localCycle029 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .gapLower 1 2]

def localCycle030 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, -2, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2]

def localCycle031 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 2, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2]

def localCycle032 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, -1, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

def localCycle033 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, -1, 0, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1, .triangle 1 1]

def localCycle034 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 1 0]

def localCycle035 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

def localCycle036 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 0, 2, -1, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

def localCycle037 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, 2, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .gapLower 1 4, .triangle 2 0]

def localCycle038 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -2, 2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .gapLower 1 4, .triangle 8 1, .gapLower 3 1, .triangle 1 1]

def localCycle039 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![0, -2, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .triangle 1 0]

def localCycle040 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, 0, 3, -2, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .triangle 1 0]

def localCycle041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 0, 0, 3, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2]

def localCycle042 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 4, -1, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .triangle 9 0, .gapLower 3 2, .gapLower 1 2]

def localCycle043 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, -2, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 2 0, .thetaLower 2, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2]

def localCycle044 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 0, 0, 0, 2, -1, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2]

def localCycle045 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 0, 0, 3, -1, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

def localCycle046 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 4, -1, 0, -2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1, .triangle 1 1]

def localCycle047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 4, -1, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .triangle 9 0, .gapLower 3 2, .triangle 1 0]

def localCycle048 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 4, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

def localCycle049 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 0, 0, 0, 2, -1, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .triangle 1 0]

def localCycle050 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, -1, 2, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 4, .triangle 2 0]

def localCycle051 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-2, -1, 2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 4, .triangle 8 1, .gapLower 3 1, .triangle 1 1]

def localCycle052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 0, 0, 3, -2, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .triangle 1 0]

def localCycle053 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1]

def localCycle054 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 3]
    constant := ![0, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 3 1]

def localCycle055 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 0, 0, 0, 3, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2, .gapLower 1 2]

def localCycle056 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 4, -2, 0, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3, .gapLower 1 2]

def localCycle057 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3, .gapLower 1 2]

def localCycle058 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 0 4, .distance 0 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 2, 0, 0, -2, 3, -1, -1, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 4, .gapLower 4 1, .triangle 5 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2]

def localCycle059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 0, 0, 3, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0, .gapLower 1 2]

def localCycle060 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 2]

def localCycle061 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 0, 0, 2, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 2]

def localCycle062 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, -1, 2, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 4, .gapLower 1 3, .triangle 1 0]

def localCycle063 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .theta 1, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![-1, -1, 2, -2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 0 0, .corridorLower 1 2, .gapLower 1 4, .gapLower 1 3, .gapLower 3 1, .triangle 1 1]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 1, 2, 3, 4], ![5, 6, 7, 8, 9], ![10, 10, 11, 12, 13], ![14, 15, 16, 17, 18], ![19, 20, 21, 22, 19], ![23, 24, 25, 26, 27], ![28, 28, 29, 30, 31], ![32, 33, 34, 35, 36], ![37, 38, 39, 40, 37], ![41, 41, 42, 43, 44], ![45, 46, 47, 48, 49], ![50, 51, 47, 52, 50], ![53, 54, 55, 56, 57], ![58, 59, 55, 60, 61], ![62, 63, 62, 62, 62]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask513

namespace Jsp404.SixWeakAllGroup02Data.Mask515
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![true, true, false, false, false, false, false, false, false, true]

def rows : RowsData := ![![2, 3, 1, 4], ![2, 3, 0, 4], ![1, 0, 4, 3], ![1, 0, 4, 2], ![0, 1, 3, 2]]

def localCycle000 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -3, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, 0, -3, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 5 0]

def localCycle002 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![0, 0, -3, 0, 0, 3, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 1, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2]

def localCycle003 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -3, 0, 0, 3, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .triangle 2 0]

def localCycle004 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -3, 0, 0, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle005 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle006 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -3, 0, 4, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .triangle 9 0, .triangle 5 0]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![0, -3, 0, 4, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 1, .gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .triangle 9 0, .gapLower 3 2]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![0, 4, -2, -1, -3]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 8 0, .gapLower 1 1]

def localCycle009 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -3, -1, 0, 0, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-3, -2, 4, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-3, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-3, 0, 4, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .gapLower 3 4, .gapLower 3 3, .gapLower 4 2, .triangle 2 0]

def localCycle013 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-3, 0, 2, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, 3, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle015 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![0, -2, 0, 3, -1, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 3, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 3, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 0, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3]

def localCycle018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 2, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 0, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .theta 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4, .triangle 2 0]

def localCycle020 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 1, .corridorLower 1 3, .gapLower 1 4, .triangle 2 0]

def localCycle021 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 1 2, .gapLower 1 4, .triangle 2 0]

def localCycle022 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -2, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle023 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 5 0]

def localCycle024 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -2, 0, 0, 3, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .triangle 2 0]

def localCycle025 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -2, 0, 0, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, -2, 3, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle027 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, -2, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle028 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, -2, 0, 0, 3, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .triangle 2 0]

def localCycle029 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, -2, 0, 0, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle030 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, 3, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle031 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![0, -2, 0, -2, 0, 0, 3, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 1, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle032 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, 0, 0, 3, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle033 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, 0, 0, 3, -2, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3]

def localCycle034 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, 0, 0, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle035 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 1 0, .gapLower 1 4, .triangle 2 0]

def localCycle036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![0, -2, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 1, .triangle 6 1, .gapLower 1 0, .gapLower 1 4, .triangle 2 0]

def localCycle037 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 6 1, .gapLower 1 0, .gapLower 1 4, .triangle 2 0]

def localCycle038 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, -2, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle039 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 3, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .triangle 2 0]

def localCycle040 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, -2, -1, 0, 0, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .triangle 2 0]

def localCycle041 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -2, -1, 0, 0, 3, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle042 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 0, 0, 3, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle043 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, 0, 4, -2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3]

def localCycle044 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 0, 0, 0, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .corridorLower 1 2, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle045 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 4, .triangle 2 0]

def localCycle046 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 4, .triangle 2 0]

def localCycle047 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 4, .triangle 2 0]

def localCycle048 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, -2, 4, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![0, -2, 0, 3, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle050 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 3, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle051 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 3, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .gapLower 3 3, .gapLower 4 2, .gapLower 1 3]

def localCycle052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 2, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .gapLower 3 4, .triangle 9 0, .gapLower 4 2, .gapLower 1 3]

def localCycle053 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-2, -1, 2, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .gapLower 1 4, .triangle 2 0]

def localCycle054 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![0, -2, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 3 1, .corridorLower 1 3, .gapLower 1 4, .gapLower 1 3]

def localCycle055 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 1 2, .theta 1, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 1 2, .gapLower 1 4, .gapLower 1 3]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 1, 2, 3, 4], ![5, 6, 7, 8, 9], ![10, 11, 11, 12, 13], ![14, 15, 16, 17, 18], ![19, 20, 21, 21, 21], ![22, 23, 22, 24, 25], ![26, 27, 27, 28, 29], ![30, 31, 32, 33, 34], ![35, 36, 35, 37, 35], ![26, 38, 38, 39, 40], ![30, 41, 42, 43, 44], ![45, 46, 47, 45, 45], ![48, 49, 50, 51, 52], ![26, 53, 53, 53, 53], ![30, 54, 55, 55, 55]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask515

namespace Jsp404.SixWeakAllGroup02Data.Mask519
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![true, true, true, false, false, false, false, false, false, true]

def rows : RowsData := ![![2, 3, 4, 1], ![2, 3, 4, 0], ![1, 0, 4, 3], ![1, 0, 4, 2], ![1, 0, 3, 2]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 6 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, 0, -3, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 5 0]

def localCycle002 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![0, 0, -3, 0, 0, 3, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 1, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2]

def localCycle003 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-3, 0, 0, 3, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 1]

def localCycle004 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-3, 0, 0, 2, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 1]

def localCycle005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle006 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -3, 0, 4, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .triangle 9 0, .triangle 5 0]

def localCycle007 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![0, -3, 0, 4, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 1 1, .gapLower 1 1, .gapLower 2 0, .gapLower 2 4, .triangle 9 0, .gapLower 3 2]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![0, 4, -2, -1, -3]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 3 3, .triangle 8 0, .gapLower 1 1]

def localCycle009 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

def localCycle010 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 4]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 4]

def localCycle011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 0 4]
    constant := ![0, -3, 0, 4, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 1, .gapLower 1 2, .gapLower 3 0, .gapLower 3 4, .gapLower 3 3, .gapLower 4 2]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 0 4]
    constant := ![0, -3, 0, 2, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 2 1, .gapLower 1 2, .gapLower 3 0, .gapLower 3 4, .triangle 9 0, .gapLower 4 2]

def localCycle013 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3]
    constant := ![-2, 3, -1, -1]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 9 0, .triangle 8 0]

def localCycle014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, 0, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .triangle 6 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 5 0]

def localCycle015 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-3, -1, 3]
    coefficient := ![0, 0, 1]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle017 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -1, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 1, .corridorLower 1 3, .gapLower 1 4]

def localCycle018 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, -1, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 6 1, .corridorLower 1 2, .gapLower 1 4]

def localCycle019 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -2, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle020 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 5 0]

def localCycle021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![0, -2, -2, 0, 0, 3, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 1]

def localCycle023 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, 0, -2, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .triangle 6 1, .gapLower 1 0, .gapLower 1 4]

def localCycle024 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .triangle 6 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle025 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 7 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle026 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, 0, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .triangle 6 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 5 0]

def localCycle027 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![0, 0, -2, 0, 0, 0, 3, -1, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 1 1, .triangle 6 1, .gapLower 1 0, .thetaOrder 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2]

def localCycle028 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, -2, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 1]

def localCycle029 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 8 1, .triangle 6 1, .gapLower 1 0, .corridorUpper 0 1]

def localCycle030 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .triangle 6 1, .gapLower 1 0, .gapLower 1 4]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, true, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 1, .triangle 6 1, .gapLower 1 0, .gapLower 1 4]

def localCycle032 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle033 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 8 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle034 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -2, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 5 0]

def localCycle035 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![0, -2, -1, 0, 0, 3, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .gapLower 3 2]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .gapLower 3 3, .triangle 8 0, .gapLower 1 1]

def localCycle037 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 2, -1, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .gapLower 3 4, .triangle 9 0, .triangle 8 0, .gapLower 1 1]

def localCycle038 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 8 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 4]

def localCycle039 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 3, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, 0, -2, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 2 2, .triangle 5 1, .gapLower 3 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 4]

def localCycle040 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle041 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 6 1, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle042 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .gapLower 1 4]

def localCycle043 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, -2, -1, 2]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 4]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 1 3, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 0 3]
    constant := ![-2, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 1 3, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 9 0, .triangle 5 0]

def localCycle045 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 8 1, .triangle 6 1, .corridorLower 1 2, .gapLower 1 4]

def localCycle046 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-2, -1, 2]
    coefficient := ![0, 0, 1]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .gapLower 1 4]

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
  | _ => none

def ids : Fin 15 → Fin 5 → ℕ := ![![0, 1, 2, 3, 4], ![5, 6, 7, 8, 5], ![9, 10, 10, 11, 12], ![13, 14, 15, 15, 15], ![16, 17, 18, 18, 18], ![19, 20, 21, 22, 19], ![23, 24, 23, 24, 23], ![25, 26, 27, 28, 29], ![30, 31, 30, 30, 30], ![32, 32, 32, 32, 32], ![33, 34, 35, 36, 37], ![38, 39, 38, 38, 38], ![40, 41, 41, 41, 41], ![42, 43, 43, 43, 43], ![13, 44, 45, 46, 46]]

theorem point_checked : leafCheckA library word rows ids = true := by decide

#print axioms point_checked
end Jsp404.SixWeakAllGroup02Data.Mask519
