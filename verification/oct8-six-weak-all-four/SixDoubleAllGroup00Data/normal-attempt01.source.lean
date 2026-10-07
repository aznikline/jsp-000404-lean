import Jsp000404.SixWeakOuterReplay
import Jsp000404.SixOuterWordCatalogComplete

/-! SOURCE_ONLY four literal catalog words. Kernel checks remain required. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

namespace Jsp404.SixDoubleAllGroup00Data.Mask000
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, false, false, false, false, false, false, false]

def rows : RowsData := ![![1, 2, 3, 4], ![0, 2, 3, 4], ![0, 1, 3, 4], ![0, 1, 2, 4], ![0, 1, 2, 3]]

def localCycle000 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .triangle 0 0]

def localCycle001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -1, -3, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .triangle 0 1]

def localCycle002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 0]

def localCycle003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -3, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 3 2, .triangle 1 0]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 7 0, .triangle 0 0]

def localCycle005 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .triangle 0 1]

def localCycle006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 0]

def localCycle007 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -2, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 6 0, .triangle 0 0]

def localCycle008 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -2, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .triangle 0 1]

def localCycle009 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -2, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 0]

def localCycle010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 6 0, .triangle 0 0]

def localCycle011 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle012 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -3, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .gapLower 0 1]

def localCycle013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -3, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 2, .gapLower 0 1]

def localCycle014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -3, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 4 0, .gapLower 0 1]

def localCycle016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -2, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .gapLower 0 1]

def localCycle017 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 2, .gapLower 0 1]

def localCycle018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 3, -1, -2, -2, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle020 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 3, 0, -2, -1, -2, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 0 1]

def localCycle021 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, -2, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 2, .gapLower 0 1]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-3, 0, 0, 3, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 5 0, .gapLower 0 2]

def localCycle024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -3, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 5 0, .gapLower 0 2, .triangle 0 1]

def localCycle025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 0]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![0, 4, -3, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2]

def localCycle027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 1, 0, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .triangle 5 1, .gapLower 0 2]

def localCycle028 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, 0, 3, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 5 0, .gapLower 0 2]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 2, 0, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .triangle 5 1, .gapLower 0 2]

def localCycle030 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, 0, 0, -3, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2, .triangle 0 1]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, 0, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .triangle 5 1, .gapLower 0 2]

def localCycle032 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -2, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2]

def localCycle033 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-3, 4, 0, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .triangle 3 1]

def localCycle034 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -3, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .triangle 0 1]

def localCycle035 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -3, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 6 0, .triangle 0 0]

def localCycle036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 3, .theta 3, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![0, 0, 1, 0, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, true, false] }
  origin := ![.gapLower 3 0, .thetaOrder 2, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3]

def localCycle037 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, 0, 3, -1, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1]

def localCycle038 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, 0, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .triangle 3 1]

def localCycle039 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 2, 0, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .triangle 3 1]

def localCycle040 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .gapLower 2 1, .triangle 0 1]

def localCycle041 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .triangle 0 1]

def localCycle042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3]
    constant := ![-1, 0, 0, 2, 0, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3]

def localCycle043 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 0]

def localCycle044 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 6 0, .triangle 0 0]

def localCycle045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 3 0]

def localCycle046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 9 1, .triangle 6 0, .triangle 0 0]

def localCycle047 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, 0, 0, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 2 0, .thetaOrder 1, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 2]

def localCycle048 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 2 3, .distance 0 2]
    constant := ![-2, 4, -2, -1]
    coefficient := ![0, 1, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 3 0]

def localCycle049 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 0 2]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .triangle 4 0]

def localCycle050 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .triangle 0 1]

def localCycle051 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 0]

def localCycle052 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 3 0, .gapLower 0 1]

def localCycle053 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -1, -3, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .gapLower 0 1]

def localCycle054 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -3, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 2, .gapLower 0 1]

def localCycle055 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -3, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 1, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 4 0, .gapLower 0 1]

def localCycle057 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .gapLower 0 1]

def localCycle058 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 2, .gapLower 0 1]

def localCycle059 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle060 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle061 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -2, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 0 1]

def localCycle062 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -2, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 2, .gapLower 0 1]

def localCycle063 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle064 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![-3, 0, 0, 3, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 0, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 5 0, .gapLower 0 2]

def localCycle065 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -1, -3, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .triangle 0 1]

def localCycle066 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 0]

def localCycle067 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -3, 0, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2, .triangle 0 1]

def localCycle068 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 1, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .triangle 5 1, .gapLower 0 2, .triangle 0 1]

def localCycle069 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .triangle 0 1]

def localCycle070 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 0]

def localCycle071 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, -2, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2]

def localCycle072 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 2, 0, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .triangle 5 1, .gapLower 0 2]

def localCycle073 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 5 0, .gapLower 0 2, .triangle 0 1]

def localCycle074 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -2, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 0]

def localCycle075 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, 0, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2, .triangle 0 1]

def localCycle076 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-3, 4, 0, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .triangle 3 1]

def localCycle077 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -3, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 6 0, .triangle 0 0]

def localCycle078 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 1, 0, 0, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .triangle 3 1, .triangle 0 1]

def localCycle079 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -2, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 6 0, .triangle 0 0]

def localCycle080 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 2, 0, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .triangle 3 1]

def localCycle081 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -2, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .triangle 0 1]

def localCycle082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 6 0, .triangle 0 0]

def localCycle083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .gapLower 0 4, .gapLower 4 0, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 0]

def localCycle084 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 7 0, .triangle 0 0]

def localCycle085 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -3, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .gapLower 0 1]

def localCycle086 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -3, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 2, .gapLower 0 1]

def localCycle087 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -3, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2, .gapLower 0 1]

def localCycle088 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .triangle 5 1, .gapLower 0 2, .gapLower 0 1]

def localCycle089 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 6 0, .gapLower 2 1, .gapLower 0 1]

def localCycle090 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 5 0, .gapLower 0 2, .gapLower 0 1]

def localCycle091 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .gapLower 2 1, .gapLower 0 1]

def localCycle092 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 0 1]

def localCycle093 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2, .gapLower 0 1]

def localCycle094 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, 0, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2, .gapLower 0 1]

def localCycle095 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -3, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle096 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, 0, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .triangle 3 1, .gapLower 0 1]

def localCycle097 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 2, .gapLower 0 1]

def localCycle098 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle099 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 2, .gapLower 0 1]

def localCycle100 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 3 0, .gapLower 0 1]

def localCycle101 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 1, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 4 0, .gapLower 0 1]

def localCycle102 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-3, 4, 0, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .gapLower 0 2]

def localCycle103 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -3, 0, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 2, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2, .triangle 0 1]

def localCycle104 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 1, 0, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .gapLower 0 2]

def localCycle105 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 4, 0, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .gapLower 0 2]

def localCycle106 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 2, 0, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .gapLower 0 2]

def localCycle107 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 2, 0, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .gapLower 0 3, .gapLower 0 2]

def localCycle108 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![0, 1, 0, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 4 2, .triangle 2 2, .triangle 5 1, .gapLower 0 2]

def localCycle109 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-2, 0, 0, 2, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .triangle 5 1, .gapLower 0 2]

def localCycle110 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 2, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .triangle 5 1, .gapLower 0 2, .triangle 0 1]

def localCycle111 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .distance 2 4, .distance 2 3, .distance 1 3, .distance 0 3, .distance 0 2]
    constant := ![0, 2, -2, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 3 2, .triangle 1 2, .gapLower 0 2]

def localCycle112 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .theta 2, .theta 1, .theta 0, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![-3, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true] }
  origin := ![.gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4, .gapLower 0 3, .triangle 3 1]

def localCycle113 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .theta 0, .distance 0 4, .distance 0 3]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 0 3, .gapLower 0 4, .gapLower 0 3]

def localCycle114 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .theta 2, .zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, 0, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 2 0, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 2 2, .triangle 0 2]

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
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 0, 6, 8, 5, 9, 6, 10], ![11, 12, 13, 14, 15, 16, 17, 18, 11, 19, 20, 16, 21, 17, 22], ![23, 24, 25, 26, 27, 28, 28, 28, 29, 24, 30, 31, 30, 31, 32], ![33, 34, 25, 35, 36, 37, 38, 38, 39, 40, 41, 42, 43, 42, 44], ![45, 34, 25, 35, 46, 37, 47, 48, 49, 40, 41, 50, 43, 51, 44], ![52, 53, 54, 55, 56, 57, 58, 59, 52, 60, 61, 57, 62, 58, 63], ![64, 65, 66, 67, 68, 69, 70, 71, 72, 70, 73, 73, 74, 70, 75], ![76, 65, 66, 77, 78, 69, 70, 79, 80, 70, 81, 69, 74, 70, 82], ![45, 65, 83, 77, 84, 69, 70, 79, 49, 70, 81, 69, 74, 70, 82], ![64, 85, 86, 87, 88, 89, 90, 71, 72, 91, 92, 90, 93, 90, 94], ![76, 85, 86, 95, 96, 89, 97, 98, 80, 91, 92, 89, 99, 97, 100], ![45, 85, 86, 95, 101, 89, 97, 98, 49, 91, 92, 89, 99, 97, 100], ![102, 34, 25, 103, 104, 105, 105, 105, 106, 40, 41, 107, 43, 107, 107], ![64, 34, 25, 103, 108, 37, 109, 71, 72, 110, 110, 110, 43, 51, 111], ![112, 34, 25, 35, 113, 37, 114, 48, 80, 40, 41, 50, 43, 51, 44]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

theorem word_catalog : word = SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (0 : Fin 62)) := by decide

#print axioms point_checked
#print axioms word_catalog
end Jsp404.SixDoubleAllGroup00Data.Mask000

namespace Jsp404.SixDoubleAllGroup00Data.Mask202
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, true, false, true, false, false, true, true, false, false]

def rows : RowsData := ![![3, 1, 2, 4], ![3, 0, 4, 2], ![3, 0, 4, 1], ![2, 1, 0, 4], ![0, 2, 1, 3]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle001 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![-3, -1, 3, -1, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 0, .triangle 4 0]

def localCycle002 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 4, -1, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle003 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, -3, 0, 0, 3, -3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle004 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, -3, 0, 0, 1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 7 0, .triangle 4 0, .gapLower 0 2]

def localCycle005 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![-2, -2, 3, -1, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 7 0, .triangle 4 0]

def localCycle006 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -2, 4, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -2, 3, -2, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle009 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![-2, -1, 3, -1, -2]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 0, .gapLower 2 2]

def localCycle010 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![-2, -1, 3, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 0]

def localCycle011 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![-2, -1, 2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .triangle 4 0]

def localCycle012 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, -3, 0, 0, 3, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 1]

def localCycle013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, -3, 0, 0, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 1 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, -3, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 2, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle015 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle016 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, -1, 4, -1, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle017 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, -1, 4, -3, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 4, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .triangle 4 0, .gapLower 0 2]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 4, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle024 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, -1, 4, -2, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, -1, 4, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .gapLower 0 2]

def localCycle027 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle028 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-3, 0, 0, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle029 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -3, 4, -1, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 0, .triangle 4 0, .gapLower 0 2]

def localCycle031 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -3, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 4, -3, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 1, -1, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .triangle 4 0, .gapLower 0 2]

def localCycle034 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 4, -1, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .triangle 4 0, .gapLower 0 2]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 3, -1, -2, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 3, -2, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle037 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 2, -1, 0, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle038 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -2, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 4, -2, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, 2, -1, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .triangle 4 0, .gapLower 0 2]

def localCycle041 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 4, -2, -2, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 2 2, .gapLower 0 2]

def localCycle042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, 2, -1, -2, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle043 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, 2, -2, -1, -3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle044 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, -3, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3]

def localCycle045 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-3, -1, 3, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 0, .gapLower 4 1, .gapLower 0 3]

def localCycle046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, 0, 4, -3, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3]

def localCycle048 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, -1, 1, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3]

def localCycle049 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, -2, 4, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3]

def localCycle050 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -2, 4, -1, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle051 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, -2, 3, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3]

def localCycle052 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![0, -2, 2, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3]

def localCycle053 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, -1, 3, -2, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3]

def localCycle054 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, -1, 2, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3]

def localCycle055 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -1, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle057 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, 0, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle058 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -3, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .triangle 4 0, .gapLower 0 2]

def localCycle060 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 1]

def localCycle061 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle062 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle063 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -3, 4, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle064 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -1, -3, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle065 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 0]

def localCycle067 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 4, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle068 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 3, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle069 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 0]

def localCycle070 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle071 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 3, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .triangle 0 1]

def localCycle072 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle073 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, -2, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle074 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -3, 4, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle075 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -3, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle076 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, 3, -3, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle077 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -1, 1, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .triangle 4 0, .gapLower 0 2]

def localCycle078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 3, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle079 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 3, -2, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle083 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .triangle 4 0, .gapLower 0 2]

def localCycle084 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .gapLower 2 2, .gapLower 0 2]

def localCycle085 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle086 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle087 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-3, -1, 3, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 7 0, .gapLower 4 1, .gapLower 0 3]

def localCycle088 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -3, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle089 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle090 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, -2, 3, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 7 0, .gapLower 4 1, .gapLower 0 3]

def localCycle091 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-1, 0, -2, 3, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 0]

def localCycle092 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, -1, 3, -2, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3]

def localCycle093 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, -1, 2, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3]

def localCycle094 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle095 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, -1, 2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.triangle 1 0, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle096 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -3, 4, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle097 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -1, -3, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle098 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, -1, 4, -3, -1, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle099 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 1, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle100 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2]
    constant := ![-2, -2, 4, -1, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2]

def localCycle101 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 4, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle102 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 4, -2, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 2, -1, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle104 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle105 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -2, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle106 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, -1, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .triangle 4 0, .gapLower 0 2]

def localCycle107 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -2, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .gapLower 0 2]

def localCycle108 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .gapLower 0 2]

def localCycle109 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -2, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle110 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -1, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle111 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -3, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle112 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 1, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle113 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -2, 4, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle114 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle115 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 7 0, .gapLower 2 2, .triangle 0 1]

def localCycle116 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .triangle 0 1]

def localCycle117 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -3, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle118 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 0]

def localCycle119 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .theta 1, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, -1, 4, -2, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .corridorLower 1 3, .gapLower 1 4, .gapLower 2 3, .gapLower 2 2, .triangle 0 1]

def localCycle120 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 3, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 3 2, .triangle 6 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

def localCycle121 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -3, 4, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle122 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 4, -3, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle123 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 1, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle124 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2]
    constant := ![-2, -2, 4, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 2 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3]

def localCycle125 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 4, -2, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle126 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, -2, 2, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 7 0, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle127 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .triangle 6 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle128 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .triangle 6 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .gapLower 4 1, .gapLower 0 3, .gapLower 0 2]

def localCycle129 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .theta 2, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![0, 0, 0, 4, -3, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3, .triangle 4 0, .gapLower 0 2]

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
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![15, 1, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28], ![29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43], ![44, 45, 46, 47, 48, 49, 50, 51, 52, 9, 53, 54, 55, 56, 57], ![0, 1, 46, 58, 59, 5, 6, 7, 8, 9, 10, 11, 60, 61, 62], ![63, 1, 64, 65, 66, 5, 67, 68, 69, 70, 10, 11, 71, 72, 73], ![74, 1, 75, 76, 77, 5, 78, 79, 80, 81, 82, 83, 84, 85, 86], ![0, 87, 46, 88, 89, 90, 6, 91, 8, 9, 92, 93, 94, 61, 95], ![0, 1, 46, 58, 59, 5, 6, 7, 8, 9, 10, 11, 60, 61, 62], ![96, 1, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109], ![63, 87, 110, 111, 112, 90, 67, 113, 69, 9, 92, 93, 114, 115, 116], ![63, 1, 110, 117, 118, 5, 67, 68, 69, 9, 10, 11, 119, 115, 120], ![121, 87, 75, 122, 123, 124, 78, 125, 126, 81, 92, 93, 127, 85, 128], ![74, 1, 75, 129, 77, 5, 78, 79, 80, 81, 82, 83, 84, 85, 86], ![0, 87, 46, 88, 89, 90, 6, 91, 8, 9, 92, 93, 94, 61, 95]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

theorem word_catalog : word = SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (17 : Fin 62)) := by decide

#print axioms point_checked
#print axioms word_catalog
end Jsp404.SixDoubleAllGroup00Data.Mask202

namespace Jsp404.SixDoubleAllGroup00Data.Mask472
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![false, false, false, true, true, false, true, true, true, false]

def rows : RowsData := ![![1, 3, 4, 2], ![0, 4, 3, 2], ![3, 4, 0, 1], ![2, 0, 4, 1], ![2, 0, 3, 1]]

def localCycle000 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -1, -1, -3, 4]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .gapLower 2 4]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -1, 0, -3, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .triangle 9 2, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2]

def localCycle002 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle003 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, 0, 3, -3]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 9 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3]

def localCycle004 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-3, 0, 0, 1, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle005 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -1, 0, -2, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .triangle 9 2, .gapLower 2 1, .gapLower 2 0, .gapLower 2 4]

def localCycle006 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -1, -1, -2, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .corridorUpper 1 2]

def localCycle007 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -2, 3, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 9 1, .gapLower 2 0, .corridorUpper 1 2, .gapLower 2 3]

def localCycle008 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -1, -1, -2, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .triangle 9 0, .gapLower 2 0, .gapLower 2 4]

def localCycle009 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, -1, 3, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def localCycle010 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, -2, -1, 3, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle011 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -1, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .triangle 9 2, .gapLower 2 1, .corridorLower 2 3, .gapLower 2 4]

def localCycle012 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 9 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle013 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-3, 0, 0, 2, 0, -1, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-3, 0, 0, 2, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 4 2, .triangle 5 1, .gapLower 0 1]

def localCycle015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle016 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![0, 4, -3, 0, 0, -3]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 4 2, .triangle 5 1, .gapLower 0 1]

def localCycle017 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 1, 0, -1, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle018 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 4, -2, -2, -1, 3, 0, -1, -1, -3]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle019 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 2, .triangle 5 1, .gapLower 0 1]

def localCycle020 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -1, -1, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, 0, 0, -3]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 4 2, .triangle 5 1, .gapLower 0 1]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -3, 4, 0, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle023 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -1, 3, 0, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle025 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -1, 1, 0, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle026 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -1, 0, -2, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .triangle 9 2, .gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2]

def localCycle027 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -2, 3, 0, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -2, 2, 0, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle029 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -3, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle030 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -1, 2, 0, -1, 0, -3]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle031 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def localCycle032 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, -1, 3, 0]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .triangle 0 2]

def localCycle033 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .triangle 9 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle034 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle036 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, 0, -2, 4, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .triangle 9 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle037 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def localCycle038 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle039 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 2]

def localCycle040 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .triangle 9 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle041 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-3, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .corridorLower 2 4, .gapLower 2 4, .triangle 0 2]

def localCycle042 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -1, -1, -1, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .gapLower 2 4]

def localCycle043 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![0, -3, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle044 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-3, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle045 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 9 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle046 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -1, -1, -1, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 6 2, .triangle 8 0, .triangle 9 0, .corridorLower 2 3, .gapLower 2 4]

def localCycle047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![0, -2, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle048 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle049 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle050 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .gapLower 0 1]

def localCycle052 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -3, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 2, .triangle 5 1, .gapLower 0 1]

def localCycle053 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 1, 0, -1, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .gapLower 0 1]

def localCycle054 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 4, -2, -2, -1, 3, 0, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .gapLower 0 4, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle055 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 2, 0, -1, -1, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 4 2, .triangle 5 1, .gapLower 0 1]

def localCycle057 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -3, 4, 0, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle058 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2, .triangle 1 1]

def localCycle059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -1, 1, 0, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle060 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -2, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle061 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -2, 2, 0, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle062 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 2, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2, .triangle 1 1]

def localCycle063 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def localCycle064 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -3, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .triangle 5 1, .triangle 1 1]

def localCycle065 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -2, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle067 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 2]

def localCycle068 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .triangle 5 1, .triangle 1 1]

def localCycle069 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 2 1]

def localCycle070 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 1]
    constant := ![-2, 0, 0, 2, -2, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .triangle 2 1]

def localCycle071 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-3, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle072 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle073 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.gapLower 2 2, .gapLower 2 1, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle074 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, -1, -2, -1, 2, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .gapLower 0 4, .triangle 4 0, .gapLower 2 1, .corridorLower 2 3, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle075 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, -2, -1, 2, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 0, .gapLower 0 4, .gapLower 2 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle076 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

def localCycle077 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![0, 4, -3, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .triangle 4 2, .gapLower 0 2, .gapLower 0 1]

def localCycle078 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![0, 0, 0, 3, -2, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .triangle 4 2, .gapLower 0 2, .gapLower 0 1]

def localCycle079 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2, .gapLower 0 1]

def localCycle080 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3]

def localCycle081 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 0 2, .gapLower 0 3, .triangle 5 1, .gapLower 0 1]

def localCycle082 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![0, 4, -3, -2, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .gapLower 1 4, .gapLower 2 3, .gapLower 0 3, .triangle 5 1, .gapLower 0 1]

def localCycle083 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 1, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 5 1, .gapLower 0 1]

def localCycle084 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![0, 0, 0, 3, -2, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 2 3, .gapLower 0 3, .triangle 5 1, .gapLower 0 1]

def localCycle085 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, 0, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .triangle 0 2, .gapLower 0 3, .triangle 5 1, .gapLower 0 1]

def localCycle086 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, -2, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .gapLower 0 3, .triangle 5 1, .gapLower 0 1]

def localCycle087 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 2, -1, -3, -1, 3, 0, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .triangle 4 0, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle088 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .theta 4, .theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 2, -3, 0, 0, 3, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .gapLower 2 2, .gapLower 4 0, .thetaOrder 3, .corridorUpper 1 3, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle089 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 2, -1, -2, -2, 3, 0, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .triangle 4 0, .gapLower 2 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle090 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 2, -2, 0, -2, 4, 0, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .gapLower 2 2, .triangle 9 1, .gapLower 2 0, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle091 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 2, -2, -2, -1, 3, 0, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle092 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 2, -1, -2, -1, 2, 0, -1, -1, -2]
    coefficient := ![0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .triangle 4 0, .gapLower 2 1, .corridorLower 2 3, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .triangle 5 0, .gapLower 0 1]

def localCycle093 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -1, 3, -2]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2, .gapLower 2 3]

def localCycle094 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 0, .distance 0 2, .distance 2 4, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 2, -2, -1, 2, 0, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 0 1, .gapLower 0 4, .gapLower 2 2, .corridorLower 2 4, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 3 2, .gapLower 0 1]

def localCycle095 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 0 2, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-1, 0, 0, 2, -2, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .gapLower 2 4, .gapLower 2 3, .triangle 4 2, .triangle 5 1, .gapLower 0 1]

def localCycle096 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -3, 4, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle097 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .triangle 0 2]

def localCycle098 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 4, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .triangle 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3]

def localCycle099 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 2]

def localCycle100 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .gapLower 2 0, .corridorUpper 1 2, .triangle 0 2]

def localCycle101 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -2, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .gapLower 2 3]

def localCycle102 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .gapLower 2 0, .gapLower 2 4, .triangle 0 2]

def localCycle103 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 4, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .triangle 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3]

def localCycle104 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 0 2]

def localCycle105 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, -2, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .triangle 3 1, .corridorLower 2 3, .gapLower 2 4, .gapLower 2 3]

def localCycle106 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle107 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![0, -2, 0, -1, 3, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 4 2, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle108 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 2 3, .theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 4, .distance 0 3]
    constant := ![0, -1, 2, 0, -1, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 1, .corridorLower 2 3, .gapLower 2 4, .triangle 6 2, .triangle 8 0, .gapLower 4 2, .gapLower 0 2]

def localCycle109 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -3, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle110 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-3, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false] }
  origin := ![.gapLower 2 2, .triangle 9 1, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle111 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 0 2]
    constant := ![-2, 0, 0, -1, 3, -3]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .triangle 9 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 2 3]

def localCycle112 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 2]
    constant := ![-2, 0, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 4 1, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

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
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 1, 15, 16, 17, 5, 6, 7, 8, 18, 10, 11, 19, 20, 21], ![22, 1, 23, 24, 25, 26, 27, 27, 28, 9, 29, 11, 23, 30, 30], ![0, 31, 32, 33, 34, 35, 36, 6, 8, 37, 38, 39, 40, 41, 42], ![0, 43, 44, 45, 46, 47, 48, 7, 8, 49, 10, 11, 12, 50, 42], ![0, 1, 51, 52, 53, 5, 6, 7, 8, 54, 10, 11, 51, 55, 56], ![57, 1, 58, 58, 59, 5, 60, 60, 61, 9, 10, 11, 58, 62, 62], ![0, 63, 32, 64, 46, 65, 6, 6, 8, 9, 66, 67, 68, 69, 70], ![0, 1, 71, 45, 46, 5, 72, 7, 8, 73, 10, 74, 12, 75, 42], ![57, 1, 76, 77, 59, 5, 60, 60, 61, 9, 10, 11, 78, 79, 80], ![0, 63, 81, 82, 83, 65, 6, 6, 8, 9, 66, 67, 84, 85, 86], ![0, 87, 88, 45, 46, 89, 90, 7, 8, 91, 10, 92, 93, 94, 95], ![96, 63, 97, 98, 99, 65, 100, 101, 102, 9, 66, 67, 103, 104, 105], ![57, 1, 71, 106, 59, 5, 60, 60, 61, 73, 10, 11, 107, 108, 108], ![0, 109, 110, 111, 46, 112, 72, 6, 8, 73, 66, 67, 93, 42, 42]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

theorem word_catalog : word = SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (26 : Fin 62)) := by decide

#print axioms point_checked
#print axioms word_catalog
end Jsp404.SixDoubleAllGroup00Data.Mask472

namespace Jsp404.SixDoubleAllGroup00Data.Mask1023
open SixOuterReplay SixWeakOuterReplay

def word : Word := ![true, true, true, true, true, true, true, true, true, true]

def rows : RowsData := ![![4, 3, 2, 1], ![4, 3, 2, 0], ![4, 3, 1, 0], ![4, 2, 1, 0], ![3, 2, 1, 0]]

def localCycle000 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -1, 0, -3, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle001 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -1, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle002 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle003 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![-3, -1, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 3, .triangle 6 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def localCycle004 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![0, -1, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false] }
  origin := ![.triangle 0 1, .triangle 6 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4]

def localCycle005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -1, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle006 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, 0, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle007 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -2, -1, 0, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle008 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -1, 0, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle009 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle010 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -2, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle012 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![-2, -2, -1, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 3, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .corridorUpper 0 2]

def localCycle013 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-1, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle014 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![-2, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 3, .triangle 6 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4]

def localCycle015 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .distance 0 3, .distance 0 4, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -1, -3, 0, -1, 4, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .gapLower 2 1, .triangle 9 1, .corridorLower 3 4, .gapLower 3 4, .gapLower 0 1, .triangle 2 1, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle016 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 3, 0, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 0 2, .triangle 3 2, .gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle017 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![0, -3, 0, 0, -1, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle018 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![0, -3, 0, 0, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4]

def localCycle019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![0, -3, 0, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4]

def localCycle020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![0, -3, 0, 0, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle021 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .distance 0 2, .distance 0 3, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 3, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 0 2, .gapLower 0 2, .gapLower 3 3, .corridorLower 1 3, .corridorUpper 0 1]

def localCycle022 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![-3, 0, 0, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4]

def localCycle023 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, 0, 0, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4]

def localCycle024 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, 0, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 2, .gapLower 2 0, .gapLower 2 4]

def localCycle025 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-3, 0, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle026 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![-3, 0, 0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4]

def localCycle027 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, 0, -3, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle028 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle029 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -3, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .gapLower 3 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle030 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, -3, -1, 4]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .corridorLower 1 2, .gapLower 1 4]

def localCycle031 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -2, 0, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle034 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, -2, -1, 4]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .corridorLower 1 2, .gapLower 1 4]

def localCycle035 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, 0, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle036 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle037 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, -2, -1, -2, 0, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 4 1, .gapLower 3 0, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle038 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -2, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle039 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle040 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle041 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -1, 0, -3, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle042 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -1, -3, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle043 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -3, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle044 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -3, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4]

def localCycle045 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -1, -1, -1, 0, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle046 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -1, -2, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle047 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -2, 0, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle048 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, -1, 0, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle049 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -1, 0, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle050 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -2, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle051 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, -1, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle052 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -1, -2, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle053 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero, .theta 0, .distance 0 1]
    constant := ![0, -2, -2, -1, -1, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 0, .gapLower 0 4]

def localCycle054 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -2, -1, -1, 0, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle055 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .zero, .theta 2, .distance 0 2]
    constant := ![0, -2, -2, 0, 0, 1]
    coefficient := ![0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0, .thetaUpper 2, .gapLower 2 4]

def localCycle056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![0, -2, 0, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4]

def localCycle057 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, -1, -2, -1, 2, 0, -2, -2, 4]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 2, .gapLower 0 1, .gapLower 0 0, .gapLower 0 4]

def localCycle058 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, -2, -1, -1, 0, 2, 0, -2, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 3 2, .gapLower 0 1, .gapLower 0 0, .gapLower 0 4]

def localCycle059 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![-2, 0, 0, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4]

def localCycle060 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 1 3, .distance 2 3, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, 0, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 0 2, .gapLower 3 3, .triangle 6 1, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle061 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, -2, -1, -1, 0, 2, -2, 0, -2, 4]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 0 2, .triangle 5 2, .gapLower 0 0, .gapLower 0 4]

def localCycle062 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, 0, -3, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle063 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle064 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -3, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .corridorLower 2 3, .thetaOrder 1, .corridorUpper 0 1]

def localCycle065 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, -3, -1, 4]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .corridorLower 1 2, .gapLower 1 4]

def localCycle066 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle067 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 0, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle068 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .corridorLower 1 2, .corridorUpper 0 1]

def localCycle069 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, 0, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle070 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle071 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, -2, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .gapLower 4 1, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle072 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, -2, -1, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .corridorUpper 0 1]

def localCycle073 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, -2, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle074 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .corridorUpper 0 1]

def localCycle075 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -1, -3, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle076 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -3, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .corridorLower 2 3, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle077 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -1, -2, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .gapLower 2 1, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle078 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -2, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle079 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![0, -2, -1, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 0 2, .gapLower 2 3, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle080 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -1, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle081 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -2, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -1, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle083 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-1, -2, -1, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle084 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .theta 2, .distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-1, -3, -1, 3, -2, -2, 0, -1, 3]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 0 2, .gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle085 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, -2, 0, 0, -1, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle086 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![0, -2, -2, 0, 0, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 2, .gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle087 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, -2, 0, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .gapLower 2 4]

def localCycle088 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![-2, -2, 0, 0, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle089 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .distance 0 2]
    constant := ![0, -2, 0, 0, -1, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false] }
  origin := ![.triangle 3 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .corridorLower 2 4, .gapLower 2 4]

def localCycle090 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .distance 2 4, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 0, 0, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3, .triangle 3 2, .gapLower 0 1, .gapLower 4 3, .triangle 7 1, .gapLower 2 0, .thetaOrder 1, .corridorUpper 0 1]

def localCycle091 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 1 4, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 0 3, .triangle 3 2, .gapLower 0 1, .gapLower 4 3, .corridorLower 1 4, .corridorUpper 0 1]

def localCycle092 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, -1, -1, -1, 0, 1, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 3 2, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4]

def localCycle093 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![0, -1, -2, -1, 2, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 6 0, .gapLower 2 1, .corridorLower 2 4, .gapLower 2 4, .triangle 3 2, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4]

def localCycle094 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 0 3, .distance 0 4, .theta 0, .distance 0 1]
    constant := ![-1, -2, -1, -1, 0, 2, 0, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .triangle 3 2, .gapLower 0 1, .corridorLower 0 4, .gapLower 0 4]

def localCycle095 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, -2, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 0 3, .gapLower 0 2, .gapLower 3 3, .corridorLower 1 3, .corridorUpper 0 1]

def localCycle096 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .distance 0 2, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![-1, -1, 0, -2, 2, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 0 0, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .gapLower 2 4, .gapLower 0 2, .corridorLower 0 3, .gapLower 0 4]

def localCycle097 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2, .distance 0 3, .theta 0, .distance 0 1]
    constant := ![-1, -2, -1, -1, 0, 2, -2, -1, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 0 0, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4, .gapLower 0 2, .corridorLower 0 3, .gapLower 0 4]

def localCycle098 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, -3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4]

def localCycle099 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .distance 0 2]
    constant := ![0, -1, -1, -1, 0, 1]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false] }
  origin := ![.gapLower 2 3, .triangle 6 0, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .gapLower 2 4]

def localCycle100 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, 0, -2, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle101 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .corridorLower 1 2, .thetaOrder 0, .gapLower 0 4]

def localCycle102 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, 0, -1, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .triangle 6 0, .triangle 9 2, .gapLower 2 0, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 2 4, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, 0, -2, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 4, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

def localCycle104 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .distance 0 1]
    constant := ![-2, 0, -2, -1, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, true, true, false] }
  origin := ![.gapLower 0 3, .gapLower 2 3, .gapLower 2 2, .triangle 9 0, .corridorLower 3 4, .thetaOrder 2, .thetaOrder 1, .thetaOrder 0, .gapLower 0 4]

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
  | _ => none

def ids : Fin 15 → Fin 15 → ℕ := ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14], ![0, 15, 16, 3, 17, 5, 18, 18, 19, 9, 10, 20, 12, 20, 14], ![0, 1, 21, 3, 22, 5, 6, 23, 24, 9, 10, 25, 12, 26, 26], ![27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 34], ![41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 14], ![0, 1, 2, 3, 55, 5, 6, 7, 56, 9, 10, 57, 12, 58, 14], ![0, 1, 2, 3, 59, 5, 6, 7, 8, 9, 10, 60, 12, 61, 14], ![62, 63, 64, 65, 4, 66, 67, 68, 69, 70, 71, 72, 73, 74, 68], ![0, 75, 76, 3, 4, 77, 78, 79, 80, 81, 10, 82, 12, 83, 14], ![0, 1, 84, 3, 85, 5, 86, 86, 87, 9, 10, 60, 12, 88, 88], ![62, 63, 64, 65, 89, 66, 90, 68, 90, 70, 71, 72, 73, 91, 68], ![0, 75, 76, 3, 92, 77, 78, 79, 56, 81, 10, 93, 12, 94, 14], ![62, 63, 64, 65, 59, 66, 67, 68, 69, 70, 71, 72, 73, 95, 68], ![0, 75, 76, 3, 59, 77, 78, 79, 96, 81, 10, 60, 12, 97, 14], ![62, 63, 64, 98, 99, 66, 100, 101, 102, 103, 71, 72, 73, 104, 101]]

theorem point_checked : leafCheckB library word rows ids = true := by decide

theorem word_catalog : word = SixOuterWordCatalogComplete.wordOfMask (SixOuterWordCatalogComplete.catalog (61 : Fin 62)) := by decide

#print axioms point_checked
#print axioms word_catalog
end Jsp404.SixDoubleAllGroup00Data.Mask1023
