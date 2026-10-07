import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard019
open N4R2OuterLeftReplay

-- Cycle fingerprint 017fd3dcf939adbfd0b20bd3292193ceeab6d8064292efb594589cb87251319a.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 03898bac9fd5be64c68b9ccb0dc6f1414b90fd903268feeee836b5d0cb853386.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 1 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 03a80279cafd536a6fcf050634fbe0e8dac07f27ac87e612014f2ba526917697.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2]

-- Cycle fingerprint 06b74f9ff4c985cd7d77bdc6dd229f38f536a51dddbb534a0ac2133ca4796fec.
def localCycle00003 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 075f973072869b3ce7269e95a9e51cd8a2973d0585d05eb18320f7b2c3c77be6.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 07617771145ba941a66f3b65e3c3a62ee8d0f4e4c24c3462f48e03a46cf9d84f.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 0814c064e438431b4c8f3acdb5f1dd3604ad923e2c5a61d1f8ce6ba80c2ce2ba.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 6]
    constant := ![0, 0, 0, -2, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 29 1, .gapLower 2 1, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 17 0, .triangle 26 1, .triangle 27 2]

-- Cycle fingerprint 097a5f30fce197f40278756951ee1f8ef70d5f0960404d580382aed222acf2c4.
def localCycle00007 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0a69b1c1ad13e0d1bd12204439d96ab459c62c63c6d33af0203e5eb975063338.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 18 0, .triangle 27 1, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0aaabe792bac3fc03a36c59e6509e605be5198910c6933405e31310ea9d09d52.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .triangle 29 1, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0cea7591c182bc4a03e261a9ac700b4fafe401bfec807fabfb23dd06186754c5.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 2 5, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 0, .triangle 30 2, .gapLower 6 2, .triangle 11 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 0e889a7165c23cdfc8fd6e16ae29adb27d8b6704327907be8aa8895c2e3ec6e4.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 21 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 10be55b683ef2fae624b6cfa3e4e9f2f275cab58f883ed3d8f5561734602614a.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 10cd44cd69dce836c954ddcd43d2e6cd44519bf66564b5b68f6c8037cf5db02a.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 1116645633dd26963bd9770d3fa368f6b6ca9b5de5c38042e02672dd8097b585.
def localCycle00014 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 128ccc755a50ffcf60527ce8f02077844954a3fe25fe77128e83e96f10fe0094.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 1, .gapLower 1 3, .triangle 4 0]

-- Cycle fingerprint 1669545606e7047266e84bb34f3e3622b90d94c84a85f79c07372b91781c05b6.
def localCycle00016 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 194a8b9cf80d553a0018b667ebde1cb3d81ef0c2a38a7dc7e21c3dd863444862.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 6, .triangle 17 1, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 1953c5f33e25a95ae5e65b3b3765da3a2e9445df29075f6a7ccc8668b1b0a4b3.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 1cc5baa42d32a51123bef6d6be066a0ede97e36224bce823e07414b1d537056f.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 1de8d98f2205ca0865def05058de5ae034d77b487df811faaf494e590b7ce422.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint 1ed7ebd3832082c124356498f8ebb0764e98376258b35da09741088b1e775326.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 1fbe7eecb892757dc8632ac757ba52f41b2fc48862fd1633252ecc33fb54d57b.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2]

-- Cycle fingerprint 2052f118b84c97d8ea6ab55cf24e4c0f2594b0caf99218646fb646d0b3cd5c2b.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 20ae1454d361fc3fb2d9b37fa582f0229e8b7e32612924735687eacdea0935bc.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 20d9257309cb6d41a03eb735004b7b48c265a7f7544addc73259207ad10d4174.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 22404b30b56843c0c4dfac7cfae7a9bc13ffd9bcfcd80ca1bb12d9645ac74bc9.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint 23b1b135789554e3afbb3f25972621f7a0f773ffe5149e2adf3d2015af4e93f1.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 265bd03e7425927296adae809f6fb6f7a7dd952753bec64c8a1378399bbc81aa.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 27cd48c5765bcf35ad995f4b0800779803cd66ec0c9f2982fc5662bfe1cdc3e8.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 20 1, .triangle 21 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 28846befb3ba2481b62a18517227615f1b2d3d717b900e1f3e4df91ec768f476.
def localCycle00030 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, 0, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 2a829d6921e674f6391c1797ff602215874e5eaa411bb6819ecb952c57289cac.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 0, .triangle 26 1, .triangle 5 2, .triangle 11 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 2b2f74a7d8d5100e42e6e1668d045ab40bede8371a376d18f138b8e8ed7a99fd.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 2 3, .distance 0 3]
    constant := ![-1, -1, 0, 0, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 15 0, .triangle 5 2]

-- Cycle fingerprint 2be49b43af0eb66477303b2a63ee0aafbd6683730bce846239629eeee359ca68.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 3149abe2a5043b161757522809e62d34cd0b72757c78802004155f7f989bd4c8.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 329003f79c053100348d69674c1da371af934bfe0fc74ce50fe11a0663591268.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, -1, 0]
    strict := ![false, true, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 330d860ea8fe4b0c0090e99e308b9d0ba50526cc5e7ac8f67df34403c407f83e.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3344b7ccf28d9ea7a99c0ce15ee50a63d5bf8f5acdbe3b37315dd43902793d4e.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 33660f2e2f9ddde407bf4b22f83363d861149299d498457717cfe85572ca02f9.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3]

-- Cycle fingerprint 35abcd020ca2fcecff155af80db8b038fc73f4324e9230c6dcd961910e4b83b0.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 38486847fd41fbd915c90035089294d58e6c316d93f5c96f5118e25b0d16d403.
def localCycle00040 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 4 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 32 2, .triangle 21 0, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 38f93bc1d7bbc085c928c1183bb8eaaad79838a89b95968320d867078e7e587c.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 15 2, .triangle 19 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3]

-- Cycle fingerprint 3a02e6f00d0e0ac495527c8b1f6872d3815dfa97b04dba497e5cb7ec47824e53.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .gapLower 1 2]

-- Cycle fingerprint 3a18b8b65be2b0655f33d6d6fab02c4ac489fc1b7cdbb836456b66c5cd97424c.
def localCycle00043 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 3a27845d46ab4438b776e10853f903ef1af3b403d1790da99f831d5c6aaf0e67.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 3a62505b1dad54ebaebefc1f4f54f8b48d6ba0e448191942970076b95a84f6cd.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 6, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 18 0, .triangle 29 1, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint 3ac10ac919e4c7cd128844d3f62c602e8c9a5bdaddcaee9478a03f7f8b657c30.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 2, .triangle 19 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 2]

-- Cycle fingerprint 3e5fc975cc810d09e04085e76d8dc18dc4a4ea5a53c4011d8127a03e9cddf2e0.
def localCycle00047 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6]
    constant := ![0, 0, -1, -1, 0, 0, 3, 0, 0, -1, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 4 2, .triangle 11 1, .triangle 9 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4]

-- Cycle fingerprint 41344eb66c2a08addeed8d727d734b467588119a6b1ae4927516de741d9317bb.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 430a8de9c74b539bc4d963037677638bab26f17f8db0b3c1e6b7003980a5b450.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 21 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 431f0f152a995af9b5761718a21f9d740fa06b1e0a66f709c1997cdc59e0834f.
def localCycle00050 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 47417737775474d59e08b18ccab4d7ec0492e3e2b6bb7b06a051d384f4190688.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint 48f840445e056a49a28b70b3c2b68a7a9603f181be1c81f30a1c3a520e05a240.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 20 1, .triangle 21 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 490b40e8021883bbb526e78505cc2c45e49ebd329a44b449157ab41e535f9db7.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 4aaaf09b2ac4e1c9d02f146400a8716fc06ac5737efc744094c2557ffa0355bc.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint 4b2e0fd824bec015c44d475d0cfbae26ccebbf975a946d519dd5cd8aeb38cd73.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4b829822598ea7d6413eb2eee505522387e7571441516d554de07fb8f4b73e31.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .gapLower 3 0]

-- Cycle fingerprint 4e790e21c8e7bd2dbc3be2f430d2811080496831332c9fddc699229d1d6a2457.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, 0, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .gapLower 2 1, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 4ec1cc0cfe6ccd7da74d7dabcea8cae304271407b6c15e8bfbba207d6f37ada4.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 3, .distance 3 6]
    constant := ![0, -1, 0, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 1 2, .triangle 11 0]

-- Cycle fingerprint 4f265f14108ba7dd00375894ea0871badc815a2170ee10e13661d0c5d3ef73bb.
def localCycle00059 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -3, 0, -1, -1, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 1 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 4f337a392cde1aff53054005ed5c3801b3459a6b61c01b99843614ec976daefd.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 4f68588fd573d426c8f8cc7766f2350f95251c5e481a21e1e1cbf1856eb28882.
def localCycle00061 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .triangle 21 1, .triangle 19 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 50868a204e56eb51ce3b0d4f6c92cd2b5f5c49daefe7cf23fbe61293465ec561.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 51a6d8af245decf7a36617585fef1d66c6590511624b6432a3789d488fe81e27.
def localCycle00063 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 10 0, .triangle 11 0, .triangle 32 1, .corridorLower 3 4]

-- Cycle fingerprint 5251ae0bbcd13b908d20bd5bba97db2c20bdaf8e6d4e523b9006f75d6994fd7b.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 52921440addfaf86e8b37e2a40f12ad85c96991e3fdae965b39abdadff4d53ee.
def localCycle00065 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 52a2a24e181efa4f9c2f64aea49be8c5cb84689b5e8c2fdbf26ec6a7bcb16f94.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6]
    constant := ![-1, 3, 0, -1, -3, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 33 1]

-- Cycle fingerprint 53025ec84d13af688cacc24536731a8140acd17911f12c724efecadaa8b79a1c.
def localCycle00067 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 2, .distance 2 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 2, .gapUpper 2 2]

-- Cycle fingerprint 54c12301ae10cb84711af5bee7ab0a9b3fc431abeac57e7c8d34966fd454a313.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![0, 0, 3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 1 2, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 5572fedfb311973e9784ac6707c137fe4be5c5aa36fa014c211e001af31c4d21.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00070 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 559d25a07e8fbccc1687f20d12bd3fd043cac38c882cf7d1235604f6d62123f6.
def localCycle00071 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 57fd3811488d677dc71fcfa305283c9e24a37590eb5a81f2fd138fca83100f4a.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 58c2df332ee1d829d09cc426a2d4f0b5dfec88951d345475ad1a78a5f8cee68c.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 58ea167ee6847aa7a2642a869da038cf44afe11882bf03c25f498f780ac81964.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 16 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5989a94c01118eccc4dfc095fcb449ea2b0829adee6d2f5515a145ae7a962a1f.
def localCycle00075 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 59c4d93f628e0b933b4a6f519dfaecb6fb6afc2e9d55aaba9fc6bd4bd2dac7b8.
def localCycle00076 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 5ca896964e3f70182a9cd49811c227b10757cdb8ef8c4bac93f74f526a87c906.
def localCycle00077 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5f6bf37f160a2a1e37fe37f58d10aa15cd070b7609679a8691d467772e0d209d.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 5fa08e5f8fce9a084dee036965b5918e798a71a941e1a232ee413a7d6b07f1df.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 6]
    constant := ![0, -1, 0, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 11 0]

-- Cycle fingerprint 5ffd02e2fca94ef88518d4031074c8aabb8c6696236d26f3b65ef6ce5981976f.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 60171e38f13fa758a7244d9562a23afc62d2d11d7b20b97bc169161a8f1aa609.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 608ad088f43e2f5d589fe411e045a83db84e857729c499904adec49cc9ba9d02.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 60e62567abc54319441fafceaa001d75c8f0c5b01d050f7aea738949a6c60e3c.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 0, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 6230d942593691bef280046360890cd1c7d369ea0b4e43fbc53264f94d3f49b2.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00085 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 66f24af50022eb88232212f24afb37f6cbf0ecbe3f5407746adea53ee2fbebb5.
def localCycle00086 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 67b9e8281326d6aaaf7e1b3d0aee7d6e518ebb44f2e2b289671765b5f8fec61f.
def localCycle00087 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![0, 2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false] }
  origin := ![.triangle 19 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 690ce7cac235eba36a6b36561041a193e8d1145a7a5fbf70936880ca96d24c6f.
def localCycle00088 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 6a299b2bac2a9cbc5f6178ff6532e9e737639de1ae98b12674dd4e3c864b98ba.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 21 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint 6d4a79fa4e7d2c0d13f78cf501a8168712bc35494a0e49570e067ac2a3a0ea42.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 6d677d8c6bf6454300288ac8dbe4db46184f638d01565778794da77c25a3c5b5.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 6d8c2ca3b001b27079eac63e5d808bd4a2a1c508744e54a9c0aa31402d12598c.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 6fe4ce711cc64f5b2bbc3c722cc1f666249d237923798cd9e3f8780117bc2ed1.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 7041bf0a19839add9939a5edf6eb7334f1d73e4db25f38e33be04c02825d29f2.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 2, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3, .zero]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 32 1, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 71950e6ec3744598a746a6a7ab537b2790f3e1b7fa280334b861aff7c1d33c2f.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 71d3ee227955f3892aaf3d2f9fa1c30c182fb2efa6664f7a6d697ee8752df797.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, 0, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 1 2]

-- Cycle fingerprint 7293feb07c9712cca201bdc90dc2984f7a952350183ada778dcb475cbbc6041e.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 15 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 7332b62ca744d640a02a9f152b637d359b0372d89a55c5e3eadef335593425f4.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![0, -3, 0, 0, 0, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, true, true, false, false, true, false] }
  origin := ![.triangle 15 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00099 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 75c0e8b1c6c25c2b879fc73fdc40f06631e138700ab1df1185c35d98f3b8f8dd.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 76335023f0c904c6f261277a59d066730548bd5d4ff74d3926a07eecba2bcb59.
def localCycle00101 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 7730149eb2ef3300b23bc7a15d8838bf4e256e8e5db9ece57d2cf78254274467.
def localCycle00102 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint 78a22de08a9d92baaab88d3e5ed0e9f1da0ef7cc76f7cc234f00c2a5e6dcaa10.
def localCycle00103 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1]

-- Cycle fingerprint 78d2f08c5b526127ee45709130008e2ecf19a7cf80bd83a410cb680f6e2998a0.
def localCycle00104 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3]
    constant := ![-1, -1, 0, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 15 0]

-- Cycle fingerprint 7ae398ef822b806ae8ffde9219bfd77a37f671e9ccdb949f7d1ceb32c74a4567.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![-1, 0, 3, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint 7bf73d26a67191e4f571d6dfff9977f76a313d71928e05c71998a008bcce1169.
def localCycle00106 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 1 2, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 7f71a21734afcf5308d4646abb219f7d5c8e9bc7d3081faac1967eb7563c3cbe.
def localCycle00107 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint 82be5e13e5a977f4d67abef83066370c2e7f1a10733a3916755b6ea8dea421af.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, 0, 0, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 842dd7fbc0e9b2fdaafb263455ffd671cbfb59c71a24f3bba60a3a6580b44fd0.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8439d1eab1143968d46ee4ee17645c509b8226f6dcf032d50648967b27818351.
def localCycle00110 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, -1, 0, -1, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .triangle 15 0, .triangle 25 2, .triangle 6 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 85c1935f5e883ad41b8456fca1a73e5cb8d6ba7f3cd80c5fc29a65b665121f9e.
def localCycle00111 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint 876478524533eb047934861c3e4db5b7497de160829369568cd805b9bbcb2621.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 882f379d5bed33b21bc86bd96f714f14b1e0b323afa57d9a22a6f0f5d8ca19d0.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 886737ed5328f6a2f835049a98fd4db6d6c3bb0260a7e665f22096ae34d86a50.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![0, 0, 3, 0, 0, 0, -2, -2, -1, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Cycle fingerprint 8b3733cedbe5e7e55f940e933aa52fa6dd04c525909a46b5252eb2c3e8440e43.
def localCycle00115 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6]
    constant := ![-2, 0, -1, -1, 0, 0, 3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 1 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2]

-- Cycle fingerprint 8de1faaea18a6a47e866dad4f3862078f6b8cd524b6143132a3a5308b3152b0f.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 8f198fbbd6d29580417f5fddb2cbfeaef330719042a0d5067b0b6bacf8806ad3.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 8f2eeb5ae75bb6e9da09a8813a52a5cdf4e39204132008096a4747793b2771f7.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 2 3]
    constant := ![-1, -1, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint 8f347d66e53761bc91fe7c970082a149afb8864af5ba3f94e457fc212e594a14.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 8f96d0e2b98972cda38b54f9bd12365c68d4a1a6478b942358165d793dc26b3c.
def localCycle00120 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2]

-- Cycle fingerprint 906271ff6ba68fa2799dc2ee6bab68cf001ce2de9bf29f3f2629ac07fdb85819.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 91424af3322832163fdadc3061ca85ed65e08b051fce299e5f4904832e5601cf.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 9163adf616f851d8a22af0c1f19fa7398c4f9db13087b12e80515877f813db64.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint 92b7da1d8b1843318fc39582d0e698d3a5bd5a9b530917effadae71095813ea0.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 92fb944e9a156b4e85d5610b24bdae4843615f07bf39e6fb80bcbe3dfa3cdcdb.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4]
    constant := ![-1, 4, 0, -1, -2, -2, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorLower 3 4, .gapLower 3 6, .gapLower 5 4, .triangle 17 0, .gapLower 1 4, .gapLower 1 3, .triangle 1 2, .triangle 9 0]

-- Cycle fingerprint 94325c6fc08a66f0784f0018e6b74a842186ff5b7d9cab02ea620812cd621a69.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 948057cfd7e9e89fd1ef059a8629ca6b07c6e47f58867b2a9d2fc25db7b19b18.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 19 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 95030b2f76be90a6f1f0d34eb9053df02ec232f2056f7c8d01b61629c1a14f07.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint 96b158294cfb67ed56f3acb12421593a0d8efafafa07e89353f615835089bbaf.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, -1, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 2, .triangle 6 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 96d40c80bd3bb1800d3256e112ea37e5f25b40bea4143715f247c5d135fca736.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![0, 0, 3, 0, 0, 0, -3, 0, -1, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 3, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Cycle fingerprint 99ad453d6e27f33cb1316f73d871b307dc573e79a3fad75d581fc3dc8de305be.
def localCycle00131 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, 0, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 9a966551bd19b9c48dbd478430497ec0cec091fbe8b4e7a84bd3462c290240a3.
def localCycle00132 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9cf0df6aa8aac1982e4569139ba6ddf92f725856bc60710f642d891451a94985.
def localCycle00133 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint 9cf40d19c063645e9ced8742f4820f510c7030e0c6885469a82cd3a13bd031a9.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 9fafb946cde7879d5ffc88050e3232fec5fabdd4acac8fc3d543e03fda62cdbe.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint 9fbac923d0f87d315e283c9f566b74147437ad2f30502d7029750d52994ec5b0.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5]
    constant := ![0, -1, -2, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, true, false, false] }
  origin := ![.triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5]

-- Cycle fingerprint 9fe31e95de88d69ba152b4033dc91c7702e14497fe5724de14b051c2ed11cabd.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2]

-- Cycle fingerprint a145847bbe46d48a070bf12954f7b7c245d4854e31264fa44eb1e172e8cf959f.
def localCycle00138 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint a1a4b14ece60b77f9caa3a4bdd7cc4a273fae774ace9b70686083b3b17914f2b.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .zero, .theta 1, .distance 1 2, .distance 1 5, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, 0, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 9 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 10 1]

-- Cycle fingerprint a1e209b5fc2058bebc60d04003323d7fb4c742397a1c603c378fef9ba1ae1c7e.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint a25fca8a8a8e733ca33dc4e7dcac28bce8c6bf2eb552d64686e643f48f2c91bf.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a3bf77dea82d8e2ca4b8a04950bd65e5470e10c1d5dbebc41bf3f24fef89f1f4.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint a3d9bf09025ae005cb3db7d2cb97a84b8f8ada4ef918d10c6090c44e618df284.
def localCycle00143 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint a487039b5a639ba9541cfc52afbee1e6d2065dc547f258d7518e01e28edaab3e.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a72ade69552377e20fc3f3b768c4e75a232597dc01c5abad19c70fb6d3c3ec5a.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint a74fbb609bb4fdab47f44b1a369af62a9bf97d9e8f48224b0a9190ccb22fb352.
def localCycle00146 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, -1, 0, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint a77122489165686c8444a93240c7fa1b855ea8220b08c7f5e0551b25ff1b4762.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint a841107a34fda27fe2c4ee92a0c9c3c88a8726a4f018e565abcfb016c1cfcc6b.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint aa3c93efab8c7a785401775c53e9d271441ab1c196347f3be43e570f5c8565f3.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ac823e404a58195b290dd8d99fdad4077466852e79489aad55d036ca3f887f53.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 2, .gapLower 1 4, .triangle 1 2, .triangle 11 0, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint ad2f76d02617eadb6fc5ae9b1ecc129ecee73c14b94bfa26dd0b50762b098b04.
def localCycle00151 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint add0069579fd2bf18970a186a84b856219c6795f92ea2428f9694c346fd051b9.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, 0, 0, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint b099a4f9e2ac03aaa9a3a8633789f5ed258bc6d8279af163b4417678c40ea437.
def localCycle00153 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 1 2, .triangle 9 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 5]

-- Cycle fingerprint b2b7a72dee53c54df30055e541e10b90a8c750fb861777a572da46471507dd08.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint b31843cd0d4223406b3ea6e191706461a5511f26371df9d03e70a9e9d3b05a09.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 0 0]

-- Cycle fingerprint b432804b4a29924b13e0498089b58fbd86a84910e76e670c19b32206caefa9b8.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b58394eede92a985ae70e831d622644933655bd3293168e80a8ce189bbb28f35.
def localCycle00157 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b776a70d27d0259a21ea0a1cdd01c749a36b3cea3cfdd6e35e020fa872c80ecb.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint b8fec2bbca64da16430391d161822ef280dcb6e77d31b903fdb98e146a5c4ada.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 33 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint b93b238a7206ce3294287134faa8f86cd5f789d1e566ae94f28ffd72627928d0.
def localCycle00160 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint baeedc7bc0e5a5d9dc67bcc06ded1995456686d553282f98d5ddfd35a1d500ba.
def localCycle00161 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint bc95d2dc63ecfec8429102dbe48186fee23b563d5a741c912e2c875da69e106d.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint be78bd4f89101dbd402a5721346509a8681803ac1179ad9d21b49886bae8f2c6.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint bedb7b72619196d5aa5287b289d8ceeeae841a29b7a8c737d8717cc822f60790.
def localCycle00164 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint bf4b4eabf4cdaf052d46aca41818bc53e220a168f0c9fcb57e08c80bca4be151.
def localCycle00165 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 5, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint bf9e981f3be9c2cc70f74cb9a6e6fb3f31794b4ebd637fa1206cf2ef9002eecc.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint c022060427236137f0a9e4e62c500382fa4a973b131a68ea515b954e70d553cc.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 0 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 15 1, .triangle 16 0, .triangle 6 2, .triangle 9 1, .corridorLower 3 4]

-- Cycle fingerprint c19c96db57d01680f6d674b558fa7150f5a5e6860329985c0bc5acefcac79073.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint c1a387d9c8e72670a38528e4f97976f1465cd2f21daacf81ab1f9c821aa2272a.
def localCycle00169 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -2, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint c40be764e2f86e6b480a955212c9764be719fb33cb91698febc1066889394126.
def localCycle00170 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint c42b82e4fc25d052be6cf117681d285d1d4de67c06773062e44e5736c2f29d7b.
def localCycle00171 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4]
    constant := ![-1, 0, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 1 2, .triangle 9 0]

-- Cycle fingerprint c44756e5b13bc3e7ab74c4d1866876fcbad20afcbd2fdfc42bdb7976c13f35bb.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c64300c403c1ab24aac4c618a8668ab3756c789f8c3652826fef8ee5cd9a282c.
def localCycle00173 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 6, .theta 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6]
    constant := ![-1, -1, 3, -1, -1, 0, -2, 0, 3, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, -1, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false, false] }
  origin := ![.triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 2, .gapUpper 6 6, .thetaNext 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0]

-- Cycle fingerprint c8b3370cf224ff9d608828c159267aed954820da39caddd8d4b685284cbcc93f.
def localCycle00174 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c98a262192c38b0ac98b5b19d92c20c28766a7a6d86e7f8abca1ce898c5f511a.
def localCycle00175 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint cb4a20e41896ac38bc7530538c88fd912d3474b17aaff2acb238ca68b2be72f5.
def localCycle00176 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4]

-- Cycle fingerprint cc4f6a732c6fd94c801da2bb8a32121e399e36abd2875d04c16011ae415d4084.
def localCycle00177 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, 0, -2, -1, 2, -1, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, false, true] }
  origin := ![.triangle 20 0, .triangle 21 2, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint cc90f9795b4ddf3b40f4938ada69a57cf7ad9de9d5df30d20f9676a5c9c033fe.
def localCycle00178 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint cd2b89ab1947b4fb599ebd684fef1c759f5d46614a67db9512c3664d06b234da.
def localCycle00179 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 21 1, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint cfe533ee8d006e7891b49fc78cf79542bea998418dc6b17e0511a832163bf4b0.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 2, .triangle 33 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint cff794b22c5bad77dccc3d119150c18ae2fc30b232de9dc2419f990272dd17cd.
def localCycle00181 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d09ade21fe002d1af709069de77008c31d7086fb9b95bc6348c03aa3bbb6e27e.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint d14fe1f50bca2566b0d4451dd2a8ae8d0ffaa152626b1929e06ef3b011adf475.
def localCycle00183 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 2, .distance 1 3, .distance 2 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint d43dbfc69b4e2ed85dce24e986e9255695c33874c9753fcbc520c920e728a73a.
def localCycle00184 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, 0, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint d4a0e4ca89b9dd1dd0d537294ea9d2d10fe9eaa7bd9574e505f234665e159d43.
def localCycle00185 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0]

-- Cycle fingerprint d4f0eecebf98de79ea7098954253390365c952638823c6d8d4ac95e00d60a416.
def localCycle00186 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint d5a9ed10343d38e1f279c9d0f6c990d1bc8704b699f41789fd5a599420c2d2f9.
def localCycle00187 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint d5d571e721e52b768c7fdbb567b7e6ec152f28fab9e0af858b7ccba5d44f30cd.
def localCycle00188 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .zero, .theta 1, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, 0, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 9 0, .corridorLower 3 4, .thetaLower 3, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint d5f40763bb168e318e78b818383954500ffe3337ad609bf91b101a596794b4df.
def localCycle00189 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 2, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 2, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.thetaUpper 2, .gapUpper 2 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d6fce871239bcfda648caa514a02291e5074fb25ea88e3e51e02003a946d6fdd.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint d745834d3dd17a8cdc1f97b260c8cde7e7153e1cca86bbb8d622c104bb683d41.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint d88f04987d79d6409a33ac9e3fb0576d239545a1b060f74f5dfd97c4f8b99ae2.
def localCycle00192 : Cycle where
  length := 5
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 4 6]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false] }
  origin := ![.triangle 32 2, .gapUpper 3 3, .gapLower 1 4, .triangle 16 0, .triangle 29 0]

-- Cycle fingerprint dade50906a1d124992eb56580878c60fb65c9474aaa6f3e719413d3e4fc2ceaf.
def localCycle00193 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 2 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6]
    constant := ![0, 0, -1, 3, -2, -2]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 18 1, .triangle 27 1, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint daf6a251c176425577aaed43e9670dbf6494583ea9cb37d9f61029309ee4e7c6.
def localCycle00194 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .triangle 32 2, .triangle 21 0]

-- Cycle fingerprint db557d2021a0015a51eb79918dd0707ada3688901c26e29b34d42f5b4d8bdeff.
def localCycle00195 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, 0, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 2, .gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 2]

-- Cycle fingerprint dbbea03190a4eb622ee00dcbeb45cb04ebfed092c295232583a6407a4d677e33.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint dbe105d62e9f57078e9b5dff5ec4a34935da3700703b5e4d342425adfded4992.
def localCycle00197 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, 0, 0, -1, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint dd3a3a7bde32779e6ee6a5de1188bec81c8ec0f01bc26ca6165cca191da12a0c.
def localCycle00198 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 19 2, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint ddedd9bf2d0babf7a115868b1cb0d51def2ed16005f3da434b16bd15d295f851.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint df2dfd883d8a3d7cc9d7a10e0a882b30c01a082ddac6280c0be4585de4a03048.
def localCycle00200 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint dfd318b9403c8af76a6777391919d6cf464e00df578d1ecf63e4020ac7cd6437.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint e01ab1cd83be85df42c57ae816f1996fdb9d16853d9ba2d6af39caf297cde2bc.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint e0834b03cf60b6c009ca08e76810177d96648a29209be71db52c65f934c64c54.
def localCycle00203 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e10f286ac04c10b35271e38e177909873369e47244aa0e02d2b9d82089b7a992.
def localCycle00204 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 19 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint e11aebdb8c202b3164f50c113598273cde22ec77c44b835debf110f03e2ac5c7.
def localCycle00205 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -3, 0, -1, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 5, .triangle 1 2, .triangle 11 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint e193d0879ff3cea50734111ca17dade25fd2b048a0108440e676704d1db4564c.
def localCycle00206 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint e2e7000ecc0af58d15c6ad2a7bd77eb25f765ce418497f07ce1fef91057cedaa.
def localCycle00207 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint e471f64518054bb452d9ffc8db99b7f1eb236ee34c9ad7a51ce807b06ba4409f.
def localCycle00208 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 15 1, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint e48c99b162292eaafca5a8f7094440f9be2bce44f6633cb91f4f37d116be5aab.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4]

-- Cycle fingerprint e796c38582e8186aded63eaa76132ff92991f009cfa78c29c8aad13aa75206e3.
def localCycle00210 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .theta 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, 0, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 9 0, .corridorLower 3 4, .thetaNext 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 1 2]

-- Cycle fingerprint e988d55943747bbab3fb25a36c27c82a288a10cf05422b2682cfcd771d954d7d.
def localCycle00211 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 15 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e9a7c895fa95e4121f96d5c848bec517783d32ad11bb7b7bc28f51b914dfd88a.
def localCycle00212 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint e9eb83c864ec9258956b4d9c62117aac3f8a5affdd04dc7c2487f36d32b3922a.
def localCycle00213 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .theta 3, .zero, .theta 1, .distance 1 5, .distance 1 3, .distance 0 3, .distance 3 6]
    constant := ![0, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 1, .corridorLower 3 4, .thetaLower 3, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 1 2, .triangle 11 0]

-- Cycle fingerprint ea57cd2d52dde75aebb7f35c57f86dc96e43fed5d5687e4d2929db130f2d7be4.
def localCycle00214 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint eacc4416eb8af482b2ca19673d119b8768a2e27ec5405104ddcc10039c28bdda.
def localCycle00215 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint eec9567d242dd2f42c82db86475257d3b050d1984e2364d3de40ad581f1b1b3d.
def localCycle00216 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, 0, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 29 1, .triangle 16 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint f04f61890bf2990d89e72b5117b836de9a9ecc7065fa2f69e2314e5902195936.
def localCycle00217 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint f05fcc3405ae6ccde09da54a6b8f5205fdbc34a5e8b2739869f37caac016c829.
def localCycle00218 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f131f95cabd3837880c5b2fbc7687dfdb0dd23adf17f2d1b2eae7741fa546be7.
def localCycle00219 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint f259db2d85ee04c78cabee6130c2d2784b7ad5b9c4c1447385030562daea411b.
def localCycle00220 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1, .triangle 15 1, .triangle 0 0, .gapLower 1 0]

-- Cycle fingerprint f2761e356f42e52237c9b9141dc4ccdf04a25ce2cd5f70cc9d8784702b30efda.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint f30169a7e088472ed0b87d4b7e70a3a075ff65b3ae66dee1491dcc4f6504027a.
def localCycle00222 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .corridorLower 3 4, .thetaLower 3]

-- Cycle fingerprint f33745216f35a385fb62b8d9c3d377bb75c10d3cb38e84a76a8203cb4410a703.
def localCycle00223 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint f35b45b87e24f0a7d84682a9c28019aa997214d76b64fe05898bd8b0897cc1bf.
def localCycle00224 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0]

-- Cycle fingerprint f40b9cb3ebf655ac278de1bb22132eaedff1ceed224c93fe1390397c8285d03f.
def localCycle00225 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint f5be78a0e83cdfd2bb72dee0da714939b9cb5913b9f7e710c74e935b2a13e4b6.
def localCycle00226 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 2, .triangle 23 1, .gapLower 1 2, .triangle 0 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint f69b39463683b3ea350efa854abd5dd2babb4650169138d82cc610aa351f906b.
def localCycle00227 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![0, -1, -2, 0, 0, 3, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 16 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint f7328280b73d3ff18b81c401fea5732d6d5e06ba2f0463dd16d5f92a5164caae.
def localCycle00228 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Cycle fingerprint f896482514e425ec30deab1195523434ec7a3f0f62c895b4f97e792466896251.
def localCycle00229 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6]
    constant := ![-1, 3, 0, -1, -2, -1, 2, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1]

-- Cycle fingerprint f928c59cc205f7aeb33807265e05db70f49b3e95bea71e9abe865c4699cb2af3.
def localCycle00230 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 0 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 2 3]
    constant := ![0, -1, -1, 0, 0, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, true] }
  origin := ![.triangle 5 2, .triangle 9 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 18 0, .triangle 27 1]

-- Cycle fingerprint f975993bd324764d75212dc02131fb3860e6473ce3d0ef7b201a0dbfb92b19dd.
def localCycle00231 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .gapLower 2 3, .triangle 28 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint fd53f3034cd1b31e0847311af00a82c077d7056e0a634ea2276378b705759956.
def localCycle00232 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint fddd90d4596465193b06ee2dd1b41d281c11462154ddc1ed0f77d65a09f5ef11.
def localCycle00233 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 4, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, -1, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 23 0, .triangle 32 0, .corridorLower 3 4, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .gapLower 1 4]

-- Cycle fingerprint fde9e9ef304a8369b5f29e584bf194808a04b17f7a7615a5f9f928d301e4bd8b.
def localCycle00234 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 3 5, .distance 0 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .triangle 26 1, .triangle 10 0, .triangle 9 0, .corridorLower 3 4, .thetaNext 2]

-- Cycle fingerprint fe8a143d259ac5388971fabf4c163759b849cd13ee7c0ca14d1befd8ee3a00bb.
def localCycle00235 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 2 3]
    constant := ![-1, -1, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 18 1, .triangle 15 0]

def library : Library := fun id => if id < 118 then (if id < 59 then (if id < 29 then (if id < 14 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 10 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))) else (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))))) else (if id < 21 then (if id < 17 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none))) else (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))) else (if id < 25 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)))))) else (if id < 44 then (if id < 36 then (if id < 32 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 40 then (if id < 38 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 42 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))))) else (if id < 51 then (if id < 47 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))) else (if id < 55 then (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))))))) else (if id < 88 then (if id < 73 then (if id < 66 then (if id < 62 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))) else (if id < 64 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))) else (if id < 69 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none))) else (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))))) else (if id < 80 then (if id < 76 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none))) else (if id < 78 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)))) else (if id < 84 then (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)))))) else (if id < 103 then (if id < 95 then (if id < 91 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 93 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))) else (if id < 99 then (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))) else (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none))))) else (if id < 110 then (if id < 106 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))) else (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)))) else (if id < 114 then (if id < 112 then (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)))))))) else (if id < 177 then (if id < 147 then (if id < 132 then (if id < 125 then (if id < 121 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))) else (if id < 123 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))) else (if id < 128 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none))) else (if id < 130 then (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))))) else (if id < 139 then (if id < 135 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))) else (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)))) else (if id < 143 then (if id < 141 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none))) else (if id < 145 then (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))))) else (if id < 162 then (if id < 154 then (if id < 150 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))) else (if id < 152 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)))) else (if id < 158 then (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 160 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))))) else (if id < 169 then (if id < 165 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))) else (if id < 167 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none)) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)))) else (if id < 173 then (if id < 171 then (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))) else (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))))))) else (if id < 206 then (if id < 191 then (if id < 184 then (if id < 180 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none)))) else (if id < 187 then (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))) else (if id < 189 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))))) else (if id < 198 then (if id < 194 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none))) else (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)))) else (if id < 202 then (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none))) else (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)))))) else (if id < 221 then (if id < 213 then (if id < 209 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none))) else (if id < 211 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none)) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)))) else (if id < 217 then (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none))) else (if id < 219 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none))))) else (if id < 228 then (if id < 224 then (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none))) else (if id < 226 then (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none)))) else (if id < 232 then (if id < 230 then (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none))) else (if id < 234 then (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none)) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 4, 5, 3, 1, 6], ![4, 0, 5, 2, 1, 6], ![3, 0, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 28 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2432)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 1, 6], ![3, 0, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 113 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2433)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 116 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2434)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 5, 1, 6], ![0, 3, 2, 4, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 159 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2435)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 2, 5, 6, 1], ![0, 3, 2, 4, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 141 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2436)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 5, 6, 1], ![0, 3, 2, 4, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 159 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2437)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 2, 5, 6, 1], ![0, 3, 2, 4, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 124 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2438)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 2, 6, 5, 1], ![0, 3, 2, 6, 4, 1], ![0, 2, 3, 5, 4, 1]], proof := .tail 181 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2439)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 5, 6, 1], ![0, 3, 2, 4, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 44 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2440)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 6, 5, 1], ![0, 3, 2, 6, 4, 1], ![0, 3, 2, 5, 4, 1]], proof := .tail 234 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2441)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 2, 6, 5, 1], ![0, 3, 6, 2, 4, 1], ![0, 3, 5, 2, 4, 1]], proof := .tail 160 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2442)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 2, 6, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 3, 2, 4, 1]], proof := .tail 25 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2443)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 6, 2, 5, 1], ![0, 3, 6, 2, 4, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 7 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2444)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 6, 2, 5, 1], ![0, 6, 3, 2, 4, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 156 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2445)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![4, 0, 5, 2, 1, 6], ![3, 0, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 138 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2446)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![4, 0, 5, 2, 1, 6], ![3, 0, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 24 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2447)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 231 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2448)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 5, 2, 1, 6], ![0, 3, 4, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 9 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2449)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 5, 2, 6, 1], ![0, 3, 4, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 76 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2450)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 5, 2, 6, 1], ![0, 3, 4, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 76 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2451)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 5, 6, 2, 1], ![0, 3, 4, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 215 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2452)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 0, 5, 2, 6, 1], ![3, 0, 5, 2, 6, 1], ![0, 3, 4, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 88 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2453)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 5, 2, 6, 1], ![0, 3, 4, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 88 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2454)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 5, 6, 2, 1], ![0, 3, 4, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 44 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2455)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 5, 6, 2, 1], ![0, 3, 4, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 80 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2456)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 0, 5, 6, 2, 1], ![3, 0, 6, 5, 2, 1], ![0, 3, 6, 4, 2, 1], ![0, 3, 5, 4, 2, 1]], proof := .tail 134 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2457)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 4, 3, 5, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 6, 5, 2, 1], ![0, 6, 3, 4, 2, 1], ![0, 5, 3, 4, 2, 1]], proof := .tail 86 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2458)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![200, 142, 67, 27, 59, 163, 60, 19, 26, 12, 97, 220, 50, 204, 5, 211, 20, 185, 4, 198, 103, 42, 169, 164, 37, 68, 96, 188]) }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2459)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 34 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2460)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 1, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 39 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2461)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 0 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2462)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 167 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2463)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 3, 2, 6, 5], ![0, 4, 3, 1, 6, 5], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![129, 77, 102, 183, 41, 130, 17, 43, 109, 148, 46, 110, 50, 217, 14, 46, 166, 32, 3, 195, 217, 217, 87, 14, 219, 114, 104, 235]) }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2464)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 3, 6, 2, 5], ![0, 4, 3, 6, 1, 5], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .low (![57, 30, 194, 75, 78, 107, 8, 184, 179, 122, 100, 155, 50, 217, 127, 202, 61, 230, 101, 232, 217, 40, 125, 153, 115, 84, 47, 118]) }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2465)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .low (![189, 77, 102, 75, 105, 165, 70, 43, 109, 121, 22, 161, 85, 217, 16, 33, 207, 10, 65, 217, 217, 217, 171, 210, 1, 193, 69, 139]) }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2466)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 4, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 186 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2467)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 4, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 39 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2468)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 3, 6, 5], ![0, 1, 6, 5, 4, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 1, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 1, 3, 4, 2]], proof := .tail 196 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2469)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 2, 3, 6, 5], ![0, 4, 1, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 54 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2470)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 4, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 95 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2471)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 1, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 222 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2472)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 112 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2473)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 168 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2474)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 3, 2, 5], ![0, 4, 3, 6, 1, 5], ![4, 0, 2, 6, 1, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 143 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2475)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 1, 5], ![4, 0, 6, 2, 1, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 82 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2476)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 3, 5, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 6, 1, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 228 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2477)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 1], ![4, 0, 6, 2, 1, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 203 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2478)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 4, 6, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 90 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2479)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 4, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 1, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 90 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2480)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 5, 4, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 1, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 3, 1, 4, 2]], proof := .tail 209 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2481)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 90 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2482)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 90 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2483)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 4, 1, 2]], proof := .tail 123 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2484)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 6, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 128 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2485)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 2, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 55 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2486)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 0, 6, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 218 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2487)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 4, 3, 6, 1, 5], ![4, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 174 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2488)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 4, 6, 3, 1, 5], ![4, 0, 6, 2, 1, 5], ![3, 0, 2, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 82 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2489)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 1, 5], ![4, 0, 6, 2, 1, 5], ![3, 0, 6, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 83 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2490)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 133 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2491)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 4, 6, 3, 5, 1], ![4, 0, 6, 2, 1, 5], ![3, 0, 2, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 203 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2492)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 1], ![4, 0, 6, 2, 1, 5], ![3, 0, 6, 2, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 157 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2493)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 4, 1, 2]], proof := .tail 90 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2494)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 5, 4, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 3, 4, 1, 2]], proof := .tail 209 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2495)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 90 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2496)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 6, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 0, 3, 4, 2, 1]], proof := .tail 209 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2497)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 2, 6, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 90 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2498)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 0, 6, 2, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 192 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2499)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 5, 3, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 6, 5, 1], ![3, 0, 2, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 48 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2500)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 3, 5, 1], ![4, 0, 6, 2, 5, 1], ![3, 0, 2, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 190 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2501)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 6, 5, 3], ![0, 1, 4, 6, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 1, 2, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 178 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2502)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 1, 6, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 222 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2503)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 4, 6, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 1, 6, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 3, 1, 4, 2]], proof := .tail 140 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2504)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 2, 6, 5, 3], ![0, 4, 1, 6, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 178 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2505)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 206 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2506)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 3, 2, 1, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 154 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2507)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 2, 1, 6, 5], ![6, 0, 3, 2, 1, 4], ![5, 0, 3, 2, 1, 4]], proof := .tail 162 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2508)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 23 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2509)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 3, 5, 1], ![4, 0, 6, 2, 5, 1], ![3, 0, 2, 6, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 190 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2510)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 3, 5, 1], ![4, 0, 6, 2, 5, 1], ![3, 0, 6, 2, 1, 5], ![6, 0, 2, 3, 1, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 190 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2511)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 4, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 4, 1, 2]], proof := .tail 123 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2512)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 6, 4, 5, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 3, 4, 1, 2]], proof := .tail 182 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2513)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 4, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 53 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2514)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 2, 4, 5, 3], ![0, 6, 1, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 0, 3, 4, 2, 1]], proof := .tail 182 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2515)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 2, 5, 3], ![0, 4, 6, 1, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 6, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 18 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2516)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 2, 5, 3], ![0, 6, 4, 1, 5, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 2, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 151 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2517)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 5, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 6, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 117 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2518)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 5, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 62 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2519)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 2, 6, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 0, 3, 2, 4, 1]], proof := .tail 162 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2520)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 6, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 0, 3, 4, 2, 1]], proof := .tail 93 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2521)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 4, 3, 6, 5, 1], ![4, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 2, 3, 4, 1]], proof := .tail 145 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2522)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 3, 5, 1], ![4, 0, 6, 2, 5, 1], ![3, 0, 2, 6, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 3, 2, 4, 1]], proof := .tail 212 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2523)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 3, 5, 1], ![4, 0, 6, 2, 5, 1], ![3, 0, 6, 2, 5, 1], ![6, 0, 2, 3, 4, 1], ![5, 0, 3, 4, 2, 1]], proof := .tail 156 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2524)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 2, 6, 5, 4, 3], ![0, 1, 6, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 0, 3, 4, 1, 2]], proof := .tail 72 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2525)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 2, 5, 4, 3], ![0, 6, 1, 5, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 0, 3, 4, 2, 1]], proof := .tail 53 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2526)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 5, 1, 2], ![6, 0, 3, 4, 2, 1], ![5, 0, 3, 4, 2, 1]], proof := .tail 180 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2527)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 5, 4, 2, 3], ![0, 4, 6, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 2, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 0, 3, 2, 4, 1]], proof := .tail 170 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2528)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 4, 5, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 0, 3, 4, 2, 1]], proof := .tail 56 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2529)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![4, 0, 6, 5, 1, 2], ![3, 0, 6, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 0, 3, 4, 2, 1]], proof := .tail 176 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2530)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 2, 6, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 0, 3, 2, 4, 1]], proof := .tail 162 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2531)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 6, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 0, 3, 4, 2, 1]], proof := .tail 156 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2532)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 4, 3, 6, 5], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 0, 6, 5, 2, 1], ![3, 0, 6, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 0, 3, 4, 2, 1]], proof := .tail 144 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2533)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 4, 6, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 1, 2, 4]], proof := .low (![197, 216, 67, 146, 98, 205, 79, 108, 224, 214, 227, 175, 50, 131, 74, 223, 126, 152, 64, 81, 226, 149, 201, 71, 38, 191, 136, 213]) }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2534)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 112 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2535)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 36 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2536)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 6, 3, 2, 5], ![0, 4, 6, 3, 1, 5], ![4, 6, 0, 2, 1, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 158 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2537)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 1], ![4, 6, 0, 2, 1, 5], ![3, 0, 2, 1, 6, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 0, 2, 1, 4]], proof := .low (![189, 2, 99, 66, 111, 165, 70, 137, 89, 172, 120, 161, 6, 51, 13, 49, 29, 31, 119, 11, 52, 177, 91, 15, 229, 58, 150, 94]) }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2538)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 1, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 199 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2539)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 4, 6, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 1, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 63 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2540)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 1, 6, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 106 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2541)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 4, 6, 3, 5], ![0, 1, 6, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 1, 6, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 0, 1, 4, 2]], proof := .tail 147 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2542)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 2, 6, 3, 5], ![0, 4, 1, 6, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 63 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2543)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 6, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 2, 1, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 45 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2544)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 2, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 55 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2545)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 3, 2, 5], ![0, 4, 6, 3, 1, 5], ![4, 6, 0, 2, 1, 5], ![3, 0, 2, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 92 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2546)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 3, 5, 2], ![0, 4, 6, 3, 5, 1], ![4, 6, 0, 2, 1, 5], ![3, 0, 2, 6, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 132 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2547)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 6, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 4, 1, 2]], proof := .tail 35 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2548)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 6, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 187 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2549)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 0, 6, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 218 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2550)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 3, 2, 5], ![0, 6, 4, 3, 1, 5], ![4, 6, 0, 2, 1, 5], ![3, 0, 6, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 221 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2551)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 1], ![4, 6, 0, 2, 1, 5], ![3, 0, 6, 2, 1, 5], ![6, 0, 2, 1, 3, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 73 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2552)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 6, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 4, 1, 2]], proof := .tail 225 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2553)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 2, 6, 4, 3, 5], ![0, 1, 6, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 6, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 0, 4, 1, 2]], proof := .tail 233 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2554)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 4, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 6, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 208 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2555)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 2, 4, 3, 5], ![0, 6, 1, 5, 4, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 6, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 3, 0, 4, 2, 1]], proof := .tail 233 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2556)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 2, 3, 5], ![0, 4, 6, 1, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 2, 6, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 173 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2557)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 6, 4, 2, 3, 5], ![0, 6, 4, 1, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 0, 6, 2, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 21 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2558)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 4, 6, 3, 5], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 3, 5, 1], ![4, 6, 0, 2, 5, 1], ![3, 0, 2, 1, 6, 5], ![6, 0, 2, 3, 1, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 135 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 2559)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (2432 + j.val))) (lookup j.val) = true := by
  have hjbound : j.val < 128 := j.isLt
  by_cases h64 : j.val < 64
  · by_cases h32 : j.val < 32
    · by_cases h16 : j.val < 16
      · by_cases h8 : j.val < 8
        · by_cases h4 : j.val < 4
          · by_cases h2 : j.val < 2
            · by_cases h1 : j.val < 1
              · have hj : j = ⟨0, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 0
                  omega
                subst j
                exact namedLeaf000_checked
              · have hj : j = ⟨1, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 1
                  omega
                subst j
                exact namedLeaf001_checked
            · by_cases h3 : j.val < 3
              · have hj : j = ⟨2, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 2
                  omega
                subst j
                exact namedLeaf002_checked
              · have hj : j = ⟨3, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 3
                  omega
                subst j
                exact namedLeaf003_checked
          · by_cases h6 : j.val < 6
            · by_cases h5 : j.val < 5
              · have hj : j = ⟨4, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 4
                  omega
                subst j
                exact namedLeaf004_checked
              · have hj : j = ⟨5, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 5
                  omega
                subst j
                exact namedLeaf005_checked
            · by_cases h7 : j.val < 7
              · have hj : j = ⟨6, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 6
                  omega
                subst j
                exact namedLeaf006_checked
              · have hj : j = ⟨7, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 7
                  omega
                subst j
                exact namedLeaf007_checked
        · by_cases h12 : j.val < 12
          · by_cases h10 : j.val < 10
            · by_cases h9 : j.val < 9
              · have hj : j = ⟨8, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 8
                  omega
                subst j
                exact namedLeaf008_checked
              · have hj : j = ⟨9, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 9
                  omega
                subst j
                exact namedLeaf009_checked
            · by_cases h11 : j.val < 11
              · have hj : j = ⟨10, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 10
                  omega
                subst j
                exact namedLeaf010_checked
              · have hj : j = ⟨11, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 11
                  omega
                subst j
                exact namedLeaf011_checked
          · by_cases h14 : j.val < 14
            · by_cases h13 : j.val < 13
              · have hj : j = ⟨12, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 12
                  omega
                subst j
                exact namedLeaf012_checked
              · have hj : j = ⟨13, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 13
                  omega
                subst j
                exact namedLeaf013_checked
            · by_cases h15 : j.val < 15
              · have hj : j = ⟨14, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 14
                  omega
                subst j
                exact namedLeaf014_checked
              · have hj : j = ⟨15, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 15
                  omega
                subst j
                exact namedLeaf015_checked
      · by_cases h24 : j.val < 24
        · by_cases h20 : j.val < 20
          · by_cases h18 : j.val < 18
            · by_cases h17 : j.val < 17
              · have hj : j = ⟨16, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 16
                  omega
                subst j
                exact namedLeaf016_checked
              · have hj : j = ⟨17, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 17
                  omega
                subst j
                exact namedLeaf017_checked
            · by_cases h19 : j.val < 19
              · have hj : j = ⟨18, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 18
                  omega
                subst j
                exact namedLeaf018_checked
              · have hj : j = ⟨19, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 19
                  omega
                subst j
                exact namedLeaf019_checked
          · by_cases h22 : j.val < 22
            · by_cases h21 : j.val < 21
              · have hj : j = ⟨20, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 20
                  omega
                subst j
                exact namedLeaf020_checked
              · have hj : j = ⟨21, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 21
                  omega
                subst j
                exact namedLeaf021_checked
            · by_cases h23 : j.val < 23
              · have hj : j = ⟨22, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 22
                  omega
                subst j
                exact namedLeaf022_checked
              · have hj : j = ⟨23, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 23
                  omega
                subst j
                exact namedLeaf023_checked
        · by_cases h28 : j.val < 28
          · by_cases h26 : j.val < 26
            · by_cases h25 : j.val < 25
              · have hj : j = ⟨24, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 24
                  omega
                subst j
                exact namedLeaf024_checked
              · have hj : j = ⟨25, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 25
                  omega
                subst j
                exact namedLeaf025_checked
            · by_cases h27 : j.val < 27
              · have hj : j = ⟨26, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 26
                  omega
                subst j
                exact namedLeaf026_checked
              · have hj : j = ⟨27, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 27
                  omega
                subst j
                exact namedLeaf027_checked
          · by_cases h30 : j.val < 30
            · by_cases h29 : j.val < 29
              · have hj : j = ⟨28, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 28
                  omega
                subst j
                exact namedLeaf028_checked
              · have hj : j = ⟨29, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 29
                  omega
                subst j
                exact namedLeaf029_checked
            · by_cases h31 : j.val < 31
              · have hj : j = ⟨30, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 30
                  omega
                subst j
                exact namedLeaf030_checked
              · have hj : j = ⟨31, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 31
                  omega
                subst j
                exact namedLeaf031_checked
    · by_cases h48 : j.val < 48
      · by_cases h40 : j.val < 40
        · by_cases h36 : j.val < 36
          · by_cases h34 : j.val < 34
            · by_cases h33 : j.val < 33
              · have hj : j = ⟨32, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 32
                  omega
                subst j
                exact namedLeaf032_checked
              · have hj : j = ⟨33, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 33
                  omega
                subst j
                exact namedLeaf033_checked
            · by_cases h35 : j.val < 35
              · have hj : j = ⟨34, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 34
                  omega
                subst j
                exact namedLeaf034_checked
              · have hj : j = ⟨35, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 35
                  omega
                subst j
                exact namedLeaf035_checked
          · by_cases h38 : j.val < 38
            · by_cases h37 : j.val < 37
              · have hj : j = ⟨36, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 36
                  omega
                subst j
                exact namedLeaf036_checked
              · have hj : j = ⟨37, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 37
                  omega
                subst j
                exact namedLeaf037_checked
            · by_cases h39 : j.val < 39
              · have hj : j = ⟨38, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 38
                  omega
                subst j
                exact namedLeaf038_checked
              · have hj : j = ⟨39, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 39
                  omega
                subst j
                exact namedLeaf039_checked
        · by_cases h44 : j.val < 44
          · by_cases h42 : j.val < 42
            · by_cases h41 : j.val < 41
              · have hj : j = ⟨40, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 40
                  omega
                subst j
                exact namedLeaf040_checked
              · have hj : j = ⟨41, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 41
                  omega
                subst j
                exact namedLeaf041_checked
            · by_cases h43 : j.val < 43
              · have hj : j = ⟨42, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 42
                  omega
                subst j
                exact namedLeaf042_checked
              · have hj : j = ⟨43, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 43
                  omega
                subst j
                exact namedLeaf043_checked
          · by_cases h46 : j.val < 46
            · by_cases h45 : j.val < 45
              · have hj : j = ⟨44, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 44
                  omega
                subst j
                exact namedLeaf044_checked
              · have hj : j = ⟨45, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 45
                  omega
                subst j
                exact namedLeaf045_checked
            · by_cases h47 : j.val < 47
              · have hj : j = ⟨46, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 46
                  omega
                subst j
                exact namedLeaf046_checked
              · have hj : j = ⟨47, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 47
                  omega
                subst j
                exact namedLeaf047_checked
      · by_cases h56 : j.val < 56
        · by_cases h52 : j.val < 52
          · by_cases h50 : j.val < 50
            · by_cases h49 : j.val < 49
              · have hj : j = ⟨48, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 48
                  omega
                subst j
                exact namedLeaf048_checked
              · have hj : j = ⟨49, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 49
                  omega
                subst j
                exact namedLeaf049_checked
            · by_cases h51 : j.val < 51
              · have hj : j = ⟨50, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 50
                  omega
                subst j
                exact namedLeaf050_checked
              · have hj : j = ⟨51, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 51
                  omega
                subst j
                exact namedLeaf051_checked
          · by_cases h54 : j.val < 54
            · by_cases h53 : j.val < 53
              · have hj : j = ⟨52, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 52
                  omega
                subst j
                exact namedLeaf052_checked
              · have hj : j = ⟨53, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 53
                  omega
                subst j
                exact namedLeaf053_checked
            · by_cases h55 : j.val < 55
              · have hj : j = ⟨54, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 54
                  omega
                subst j
                exact namedLeaf054_checked
              · have hj : j = ⟨55, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 55
                  omega
                subst j
                exact namedLeaf055_checked
        · by_cases h60 : j.val < 60
          · by_cases h58 : j.val < 58
            · by_cases h57 : j.val < 57
              · have hj : j = ⟨56, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 56
                  omega
                subst j
                exact namedLeaf056_checked
              · have hj : j = ⟨57, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 57
                  omega
                subst j
                exact namedLeaf057_checked
            · by_cases h59 : j.val < 59
              · have hj : j = ⟨58, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 58
                  omega
                subst j
                exact namedLeaf058_checked
              · have hj : j = ⟨59, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 59
                  omega
                subst j
                exact namedLeaf059_checked
          · by_cases h62 : j.val < 62
            · by_cases h61 : j.val < 61
              · have hj : j = ⟨60, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 60
                  omega
                subst j
                exact namedLeaf060_checked
              · have hj : j = ⟨61, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 61
                  omega
                subst j
                exact namedLeaf061_checked
            · by_cases h63 : j.val < 63
              · have hj : j = ⟨62, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 62
                  omega
                subst j
                exact namedLeaf062_checked
              · have hj : j = ⟨63, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 63
                  omega
                subst j
                exact namedLeaf063_checked
  · by_cases h96 : j.val < 96
    · by_cases h80 : j.val < 80
      · by_cases h72 : j.val < 72
        · by_cases h68 : j.val < 68
          · by_cases h66 : j.val < 66
            · by_cases h65 : j.val < 65
              · have hj : j = ⟨64, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 64
                  omega
                subst j
                exact namedLeaf064_checked
              · have hj : j = ⟨65, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 65
                  omega
                subst j
                exact namedLeaf065_checked
            · by_cases h67 : j.val < 67
              · have hj : j = ⟨66, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 66
                  omega
                subst j
                exact namedLeaf066_checked
              · have hj : j = ⟨67, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 67
                  omega
                subst j
                exact namedLeaf067_checked
          · by_cases h70 : j.val < 70
            · by_cases h69 : j.val < 69
              · have hj : j = ⟨68, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 68
                  omega
                subst j
                exact namedLeaf068_checked
              · have hj : j = ⟨69, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 69
                  omega
                subst j
                exact namedLeaf069_checked
            · by_cases h71 : j.val < 71
              · have hj : j = ⟨70, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 70
                  omega
                subst j
                exact namedLeaf070_checked
              · have hj : j = ⟨71, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 71
                  omega
                subst j
                exact namedLeaf071_checked
        · by_cases h76 : j.val < 76
          · by_cases h74 : j.val < 74
            · by_cases h73 : j.val < 73
              · have hj : j = ⟨72, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 72
                  omega
                subst j
                exact namedLeaf072_checked
              · have hj : j = ⟨73, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 73
                  omega
                subst j
                exact namedLeaf073_checked
            · by_cases h75 : j.val < 75
              · have hj : j = ⟨74, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 74
                  omega
                subst j
                exact namedLeaf074_checked
              · have hj : j = ⟨75, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 75
                  omega
                subst j
                exact namedLeaf075_checked
          · by_cases h78 : j.val < 78
            · by_cases h77 : j.val < 77
              · have hj : j = ⟨76, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 76
                  omega
                subst j
                exact namedLeaf076_checked
              · have hj : j = ⟨77, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 77
                  omega
                subst j
                exact namedLeaf077_checked
            · by_cases h79 : j.val < 79
              · have hj : j = ⟨78, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 78
                  omega
                subst j
                exact namedLeaf078_checked
              · have hj : j = ⟨79, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 79
                  omega
                subst j
                exact namedLeaf079_checked
      · by_cases h88 : j.val < 88
        · by_cases h84 : j.val < 84
          · by_cases h82 : j.val < 82
            · by_cases h81 : j.val < 81
              · have hj : j = ⟨80, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 80
                  omega
                subst j
                exact namedLeaf080_checked
              · have hj : j = ⟨81, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 81
                  omega
                subst j
                exact namedLeaf081_checked
            · by_cases h83 : j.val < 83
              · have hj : j = ⟨82, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 82
                  omega
                subst j
                exact namedLeaf082_checked
              · have hj : j = ⟨83, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 83
                  omega
                subst j
                exact namedLeaf083_checked
          · by_cases h86 : j.val < 86
            · by_cases h85 : j.val < 85
              · have hj : j = ⟨84, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 84
                  omega
                subst j
                exact namedLeaf084_checked
              · have hj : j = ⟨85, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 85
                  omega
                subst j
                exact namedLeaf085_checked
            · by_cases h87 : j.val < 87
              · have hj : j = ⟨86, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 86
                  omega
                subst j
                exact namedLeaf086_checked
              · have hj : j = ⟨87, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 87
                  omega
                subst j
                exact namedLeaf087_checked
        · by_cases h92 : j.val < 92
          · by_cases h90 : j.val < 90
            · by_cases h89 : j.val < 89
              · have hj : j = ⟨88, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 88
                  omega
                subst j
                exact namedLeaf088_checked
              · have hj : j = ⟨89, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 89
                  omega
                subst j
                exact namedLeaf089_checked
            · by_cases h91 : j.val < 91
              · have hj : j = ⟨90, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 90
                  omega
                subst j
                exact namedLeaf090_checked
              · have hj : j = ⟨91, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 91
                  omega
                subst j
                exact namedLeaf091_checked
          · by_cases h94 : j.val < 94
            · by_cases h93 : j.val < 93
              · have hj : j = ⟨92, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 92
                  omega
                subst j
                exact namedLeaf092_checked
              · have hj : j = ⟨93, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 93
                  omega
                subst j
                exact namedLeaf093_checked
            · by_cases h95 : j.val < 95
              · have hj : j = ⟨94, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 94
                  omega
                subst j
                exact namedLeaf094_checked
              · have hj : j = ⟨95, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 95
                  omega
                subst j
                exact namedLeaf095_checked
    · by_cases h112 : j.val < 112
      · by_cases h104 : j.val < 104
        · by_cases h100 : j.val < 100
          · by_cases h98 : j.val < 98
            · by_cases h97 : j.val < 97
              · have hj : j = ⟨96, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 96
                  omega
                subst j
                exact namedLeaf096_checked
              · have hj : j = ⟨97, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 97
                  omega
                subst j
                exact namedLeaf097_checked
            · by_cases h99 : j.val < 99
              · have hj : j = ⟨98, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 98
                  omega
                subst j
                exact namedLeaf098_checked
              · have hj : j = ⟨99, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 99
                  omega
                subst j
                exact namedLeaf099_checked
          · by_cases h102 : j.val < 102
            · by_cases h101 : j.val < 101
              · have hj : j = ⟨100, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 100
                  omega
                subst j
                exact namedLeaf100_checked
              · have hj : j = ⟨101, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 101
                  omega
                subst j
                exact namedLeaf101_checked
            · by_cases h103 : j.val < 103
              · have hj : j = ⟨102, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 102
                  omega
                subst j
                exact namedLeaf102_checked
              · have hj : j = ⟨103, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 103
                  omega
                subst j
                exact namedLeaf103_checked
        · by_cases h108 : j.val < 108
          · by_cases h106 : j.val < 106
            · by_cases h105 : j.val < 105
              · have hj : j = ⟨104, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 104
                  omega
                subst j
                exact namedLeaf104_checked
              · have hj : j = ⟨105, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 105
                  omega
                subst j
                exact namedLeaf105_checked
            · by_cases h107 : j.val < 107
              · have hj : j = ⟨106, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 106
                  omega
                subst j
                exact namedLeaf106_checked
              · have hj : j = ⟨107, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 107
                  omega
                subst j
                exact namedLeaf107_checked
          · by_cases h110 : j.val < 110
            · by_cases h109 : j.val < 109
              · have hj : j = ⟨108, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 108
                  omega
                subst j
                exact namedLeaf108_checked
              · have hj : j = ⟨109, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 109
                  omega
                subst j
                exact namedLeaf109_checked
            · by_cases h111 : j.val < 111
              · have hj : j = ⟨110, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 110
                  omega
                subst j
                exact namedLeaf110_checked
              · have hj : j = ⟨111, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 111
                  omega
                subst j
                exact namedLeaf111_checked
      · by_cases h120 : j.val < 120
        · by_cases h116 : j.val < 116
          · by_cases h114 : j.val < 114
            · by_cases h113 : j.val < 113
              · have hj : j = ⟨112, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 112
                  omega
                subst j
                exact namedLeaf112_checked
              · have hj : j = ⟨113, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 113
                  omega
                subst j
                exact namedLeaf113_checked
            · by_cases h115 : j.val < 115
              · have hj : j = ⟨114, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 114
                  omega
                subst j
                exact namedLeaf114_checked
              · have hj : j = ⟨115, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 115
                  omega
                subst j
                exact namedLeaf115_checked
          · by_cases h118 : j.val < 118
            · by_cases h117 : j.val < 117
              · have hj : j = ⟨116, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 116
                  omega
                subst j
                exact namedLeaf116_checked
              · have hj : j = ⟨117, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 117
                  omega
                subst j
                exact namedLeaf117_checked
            · by_cases h119 : j.val < 119
              · have hj : j = ⟨118, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 118
                  omega
                subst j
                exact namedLeaf118_checked
              · have hj : j = ⟨119, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 119
                  omega
                subst j
                exact namedLeaf119_checked
        · by_cases h124 : j.val < 124
          · by_cases h122 : j.val < 122
            · by_cases h121 : j.val < 121
              · have hj : j = ⟨120, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 120
                  omega
                subst j
                exact namedLeaf120_checked
              · have hj : j = ⟨121, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 121
                  omega
                subst j
                exact namedLeaf121_checked
            · by_cases h123 : j.val < 123
              · have hj : j = ⟨122, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 122
                  omega
                subst j
                exact namedLeaf122_checked
              · have hj : j = ⟨123, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 123
                  omega
                subst j
                exact namedLeaf123_checked
          · by_cases h126 : j.val < 126
            · by_cases h125 : j.val < 125
              · have hj : j = ⟨124, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 124
                  omega
                subst j
                exact namedLeaf124_checked
              · have hj : j = ⟨125, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 125
                  omega
                subst j
                exact namedLeaf125_checked
            · by_cases h127 : j.val < 127
              · have hj : j = ⟨126, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 126
                  omega
                subst j
                exact namedLeaf126_checked
              · have hj : j = ⟨127, by decide⟩ := by
                  apply Fin.ext
                  change j.val = 127
                  omega
                subst j
                exact namedLeaf127_checked

theorem correct (id : Fin 24698) (hlow : 2432 ≤ id.val) (hhigh : id.val < 2560) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 2432)) = true := by
  let j : Fin 128 := ⟨id.val - 2432, by omega⟩
  have hsum : 2432 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (2432 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard019
