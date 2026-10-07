import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard050
open N4R2OuterLeftReplay

-- Cycle fingerprint 025f93e1e398c0bbe59ca358d99b721933dd1180a46c05d7ef33a7ef7f384934.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 03a2bcf9b5ada66522f0840ea48b1a119a3ce059d9c6e3bc3fc3b29ce08f3044.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint 03a80279cafd536a6fcf050634fbe0e8dac07f27ac87e612014f2ba526917697.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2]

-- Cycle fingerprint 0aa225412dcc440902cd650c12713055b13b59e234af9d92f2379a5890c2275d.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 0ad19470ecc086d1f07df4c418ab98ad91ee59178a11a94da91138aff2dc69a1.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint 0be961b25cc229563c6cba0056560d1842fcb7bc0b385d13f18362d915b703a1.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0cc9a55313d20e40d18eeed31b0b218575c9a2469c9a21ae2de33cdb13399539.
def localCycle00006 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint 0f87001adf4326208981a4fe043729283fab5678a4909bb15378f78eb762efa9.
def localCycle00007 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 10abb589bd80370de9981f2fbd46997f2247a261d66e2dec72cc1ebe87f510fa.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 10cd44cd69dce836c954ddcd43d2e6cd44519bf66564b5b68f6c8037cf5db02a.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 11d2e0aa15846f984ea25cb84aaeea229d90439f22f3f192d01fc5794e254154.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4]
    constant := ![-1, -2, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 16328b0ed4968258d16b2422715346d3c21751ef58029a98a08285569a05af3c.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6]
    constant := ![-2, 0, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2]

-- Cycle fingerprint 174add3fde5153f702ed9ba55a83bcf6a016128b60e57056515dd6d33270c2d2.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 17bde90482ca8b1a5d6c9d14fa12dabbc6e06a1ce43622156397c75a1cb14273.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 18825fe1c4e18cfe5a8007cd2253a26b04506ed510f84ec9bbf169ce2e8ba9aa.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 1d64a385bfbb9bc4986f86cbff1ca2694ac5b5768a098225ba32800a366b2c6b.
def localCycle00015 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5]
    constant := ![2, 0, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 22 2]

-- Cycle fingerprint 1edb9566a130eb4dfcef6a965d24cd838bc50682fd9f99563d65ec0061a9dbab.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 18 2, .gapLower 1 4, .triangle 1 2]

-- Cycle fingerprint 20738537015d62cd5c1624adbb8cfd35039bf0bddf89ed1fc4fb30df913c9705.
def localCycle00017 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5]
    constant := ![2, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 214e7eea5fea4a8fce1bd002065461c5a4c4d9ee1e0d1057e84a1e241194cc7f.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 19 2, .triangle 22 2, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3]

-- Cycle fingerprint 21c8f6f86e326258fb211c36a59597dea0f34028cc2dbc805e06eabc893aced9.
def localCycle00019 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 23542b8fe00c1ab2a1e10b05411f8345e1040e2f73376f91043d5b266cf74a99.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 1, .gapLower 1 2, .triangle 2 2]

-- Cycle fingerprint 240063ee855dd3dfe487d8debcb1797461acded74ec4f3d7681ff597fa9dddb6.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 259c4d6caea6c043a7a6d1cab4af1ff3a9be287e9d72e36ac5be80a0a3c0886a.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 273bcf25ec29f5625804bb99b446008373590371664ced522b8f438b70ba9ba2.
def localCycle00023 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 2aa7f49736cec555282795764b2933088229d3c644cc796f07996a3c8bb5f24a.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 2b1a3202889fb47008b8ff86a7361dc2b3a236ec22f7eb629d8360c201825c56.
def localCycle00025 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 2bdf98ae72dbc332a672a39dd6075f6994cf3ec034ebfd90cc6c6920947e6657.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 2cf688c8155d7651c9b6908f5cb46738ebf3ec78f988ab9285a839df0abfc511.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 3, .distance 3 6]
    constant := ![0, -1, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 1 2, .triangle 11 0]

-- Cycle fingerprint 2d3fa5b943b6e170d318be568d1c91627709a2fd81688836b012d013e4e0fe25.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 32c95c4534eab4e82c59f6f92f4453a9551132a8030c2bff223a9195d2251c96.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 35f0c532d85a1cab11e6c1565a02772f026ad5d06fe6940788fbc465b4f56dfd.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-1, -3, 0, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0]

-- Cycle fingerprint 3686e7d86d001714ee6548897894ad65cb8ac3e38cdcc32e6a7015fda7b0d707.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 3699680e90c80a615da68fa38df1df94137241366f07ffe9eaa36b438a0efd88.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 369e2562961e2d788abc7c4b698586e10cb0c19b7f215755371e565a79ff795c.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 374cf1c3806f43f7ebd92e811e9e0274344af734e1cccd75b1d39feb067cc6bb.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 3a18b8b65be2b0655f33d6d6fab02c4ac489fc1b7cdbb836456b66c5cd97424c.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 3da2d67c1622762b47f969ecfa526e92d99ae2b0560e4a947bbc9f102e2ef6cf.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 5, .distance 3 5]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 2, .triangle 10 1]

-- Cycle fingerprint 3dda4d89b0d43dee0e9c5cb507c0399885ed2928f65b29779bc895238dda3169.
def localCycle00037 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 3f6a1d68a83919d85c8f127b747ffa40ed432645c34dd9a7013d84158923ef36.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![0, -1, -1, 3, -3, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint 408c4863744f02d2faf29409f2d5665f74bf66d13f2dfcf27af6c814c6934fe1.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint 4319aeb8c1ad173272cdb8359b694b00b916c3891475629017c24eda3f68db0a.
def localCycle00040 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 43444d2ff89a1893cdd7e4b427b559f1e4ae4400835fc0aebc79bd926848433a.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 4449d13d8b23805d142ea7f2672d0d44176fe2ea47f05694f2125eb76846e216.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint 44895357066980f36fde9005f7280c02c7485806704659c9010872dfc9f9f5be.
def localCycle00043 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint 460f71abe600a2fc5df0c0b6810a82008b1e6e29727724d9ab1048dd3d6c8698.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![0, 0, -2, 0, 0, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 20 1, .triangle 21 2, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 2]

-- Cycle fingerprint 46a99f5ff41bcf5869dc09dc2a4846b1edd184a73351dc9bf8d112003966015a.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 4706625f55a995d2c691db6b203adb79ad05330a53bcb8ca69b93da579494692.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6]
    constant := ![-1, -1, 3, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint 47417737775474d59e08b18ccab4d7ec0492e3e2b6bb7b06a051d384f4190688.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint 47fcc84c4c633fd62774720b5dcdc39dc73070bdbb0b5947d03f073f367343fa.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 20 2, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 4aee86267e54f69e74c702a1c8602fe4ad062ad99165e654e4b098f644388961.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 18 2, .gapLower 1 4, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 4b45c1e48281d4a825c1e86683c9ae925ded994d7fe482c6df2e159dcd6031da.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 4ca2a7421b3d36e40fef8291fddbc1d5a61acdc7f7ad3700f3cf09bee79dda04.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .distance 2 5, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -3, 0, 0, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 33 1, .triangle 30 0, .gapLower 5 0, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 50a0bb902577cb03e4d29ea5270e3ca2e209887448466d08ff90573481159a54.
def localCycle00052 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-3, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 522600377378e23299644792df5c5efe9075e9c88e862b17b3a138f4102f884f.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4]
    constant := ![-1, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 1 2, .triangle 9 0]

-- Cycle fingerprint 52921440addfaf86e8b37e2a40f12ad85c96991e3fdae965b39abdadff4d53ee.
def localCycle00054 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 52c679d5ab87afbb7e4d933375edd0adcc9650f6a5a82ea2bb2366a36e8de804.
def localCycle00055 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![0, -1, -1, 0, 0, 0, 2, 0, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, true, false, true, true, true, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 8 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint 52de348cbb225a94e2df097687315320de1d86f08f20619ee647d1a1aa235f2a.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 55267cb6c66fd16c3c8b745e04f30280a5bb1fa4b64467f55be65e03db92b588.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 5591e6a1d0098147bdc6ace85ad8a9d7d2c37d81d5f4a475f9205caa1d87876a.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00059 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 5989a94c01118eccc4dfc095fcb449ea2b0829adee6d2f5515a145ae7a962a1f.
def localCycle00060 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 5adad1d18f164210673fd591bed1103c2fd1feb15d0f0c7c9602e4fefee64c98.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5]
    constant := ![0, -1, -1, 3, -2, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false] }
  origin := ![.triangle 31 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 1 2, .triangle 10 0]

-- Cycle fingerprint 5ca896964e3f70182a9cd49811c227b10757cdb8ef8c4bac93f74f526a87c906.
def localCycle00062 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 6094f68ca2256e801a083237be068a72064471127353c44999bd5ff25c3d54fc.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 7 2, .triangle 10 1, .triangle 11 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 6127bf8e17c7aff901126dd5f487416b0f8735eb20d782f1584b82709f33347a.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 622d9789ef1a687e0c3b7a22189688c42b8b4cd2ffa3a75e97fa61bbf5e81c76.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3]
    constant := ![-1, 0, 0, 3, 0, -1, -2, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0]

-- Cycle fingerprint 63ecb97dd107f2a49c88ead8ae242501114aca06be7e15807eaa5386c831a311.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 657ebecc2184f686f1c7b7eae5e6868accb5c9dbda91e247f549374d67b37bee.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 6596c70c7ddf6c5d6b209ab3b3bcb857f56845f304f4d13fa7bd1ad79c2e54b7.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00069 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 6676eb405c6d6438dfc99d6beea5a8a2a26b42aaf93f8e0e2a6a1247e3b87e2e.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![-1, -3, 0, 0, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 23 1]

-- Cycle fingerprint 67695f777ba7a2a71e89ce306ea83e405917ea39c05acb310fde1883bb936dc8.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 4]
    constant := ![-1, -1, 3, 0, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 1 2, .triangle 11 0, .triangle 32 1]

-- Cycle fingerprint 6a299b2bac2a9cbc5f6178ff6532e9e737639de1ae98b12674dd4e3c864b98ba.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 21 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint 6c91c31fe68dd02be4bbb31acf88372ffc5c636d6b1320f827ea5490a4d730ba.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint 6f2d3e974ed4cc0f76b619e4f50a61858a9ae94b425295a73089eadfba2bf1d4.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 73c48962ed2a8dab75ca0a7f87cf9e8a0ffaace6151663164c79a1ee797c6668.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00076 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 74284d1296ac2ae0c4ee3fae71b63aeec0cf2c561c45e4368b24e1381ee3d888.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 758cd42858233c6d14e516966db962ac901a74f41545f8088df7d51bc43f9607.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 7730149eb2ef3300b23bc7a15d8838bf4e256e8e5db9ece57d2cf78254274467.
def localCycle00079 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint 77eb55cc3ac9e603f336be9563063a5b9907de29397bce6549fb5eca0cda7633.
def localCycle00080 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Cycle fingerprint 79a982a8784285275fa17f12e0cf9aa39190bb6fbfaf1cf35acd56d13b8bb113.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 2, .triangle 14 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .corridorUpper 1 2]

-- Cycle fingerprint 7a498080716fa90a77c4016b10a552a9eec596a8076dc31d7e9d6156575b5dd8.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 3, .distance 3 6, .distance 1 3]
    constant := ![-3, 0, 0, -1, 0, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 3 2, .triangle 10 1, .triangle 26 0, .gapLower 3 0, .gapLower 3 6, .triangle 21 0]

-- Cycle fingerprint 7c271a4ea59795d45adc24b5bd6342f099a4342231ae296b5825ee745d245ac5.
def localCycle00083 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4]
    constant := ![0, 2, 0, 0, -1, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false] }
  origin := ![.triangle 22 2, .gapUpper 5 5, .gapLower 6 5, .triangle 32 2, .triangle 21 0, .gapLower 1 3]

-- Cycle fingerprint 7d7db8d0f71a3985187b138374ef7583f337c33a881a724350bb6934ce68b3af.
def localCycle00084 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 2, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 7eeafe32bc60a533e3a34ae6c47251f0c3c7fc259da7a47b0a31cc36a01e9927.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 5]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 3 2]

-- Cycle fingerprint 7f3011751f22c86bd37d5122a8eebc60ce808c5f918a78183245c36066d7c91a.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3]
    constant := ![-1, 3, 0, 0, -2, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0]

-- Cycle fingerprint 80053f63e27339cbde2f1c1131fa50bf639a3a53fb9f7663ecb5747120f2f8af.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![-1, -1, 3, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint 80e3d7a3d1a7b2cb2a5e7c93e79fcc83d06b8e126fc547136e1e1cd6a2bcc985.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 814ccf27c01c2c7dcb50e3a781b57f85707927814841d332dff5e1624126cee8.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 842dd7fbc0e9b2fdaafb263455ffd671cbfb59c71a24f3bba60a3a6580b44fd0.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8441c9ee442003f6d00ab9c0b57cbae69a2d40b389eadbe3b075a07a3ecc4e04.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 85c1935f5e883ad41b8456fca1a73e5cb8d6ba7f3cd80c5fc29a65b665121f9e.
def localCycle00092 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint 872c40ebf9e45d147bbd8e1f9aa4980c9fdd68f70920f7f28b1fd64b7a1e0637.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 876ccc1391054478390808afbdc35e82bcf44c6bf25bc925f82b6091d4049615.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, -1, 3, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint 8a587f70b50aab7a367bdfd1e9f51c2ffcdede6c0a450a5b5508e8cf20fbdcf4.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 8ae3a218f959b045004daad190c54d6a44ca83c6ce46919ab454b4b7a9682cb2.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 10 1]

-- Cycle fingerprint 8e117147f6c77fe0eab7909af4b927227ec7b15177039aa4c86367bb32e6d968.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, 0, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 21 2, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 8eb456db86df1e90d35edd49f2462fbc778b768265a64e23223d7c705a161016.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 90b2ffde6f8806fa8b2b7d08bd74ebc97957307d7336676d430fc67dda6d3a3a.
def localCycle00099 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .gapLower 3 0]

-- Cycle fingerprint 90f659d89c11f90dbf0a18f0c94f18669d3c5819fade13de94f16acec47ac57a.
def localCycle00100 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 92cc755504f4c555c4786de0d0f699bf495457cadfa4076237ea42a53f562265.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![0, 0, -2, 0, 0, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, true, false, true] }
  origin := ![.triangle 21 1, .triangle 20 2, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint 9376066d6f0715d29fc0cbe238758dc667557d852564e6bdb9439182319694cd.
def localCycle00102 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 948419c1376c13516048912c4b372965fcfb01935e581cf43b285ecac2134120.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 3 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 5]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 10 1, .triangle 26 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 3 2]

-- Cycle fingerprint 96c98728354897a6a5752df32187d782d7fa26832c1e82e4e04fbe867404e6bc.
def localCycle00104 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 978d94b40f0ae8c444d633b61264fc09fec32e6f24c8757bac7184916738f24e.
def localCycle00105 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 993c9d8548fee0c9da3097e1e6b406b85a0c6a8347593823cd42174608dc84eb.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 9b6b1e396e370f4c1bd25476b0702f31a6f3f75b72d0726f609c090d534f803b.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -3, 0, 0, 0, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, true, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 2, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 9c09d4e1e0267a7b414f2e46ca52c2eab7a7395bb0a71d42d90293d81955e40a.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9fe31e95de88d69ba152b4033dc91c7702e14497fe5724de14b051c2ed11cabd.
def localCycle00109 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2]

-- Cycle fingerprint a0b20040c85e78ead2c9360b4ccdf697924095b1968c65b4cedc98aef6438d9a.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a36b3768c11800ed5a8b16b447c0e0472330b8ad80f70fc3d247f6a40694781e.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint a5212f35a360883fee1276fba643dec662735d36f3b99a870b6fc62a6f042d92.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 7 2, .triangle 10 1]

-- Cycle fingerprint a5fefd5770e0f95137d74db0f9a1d2906a2767eb30143b54009f108a4a587985.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint a64de0358ce18ed0d0be85b058de437a5596187c3da6de940ae54c43e52850a9.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .gapLower 3 0]

-- Cycle fingerprint a657625cbfb28854629363e5cd14dd35745eb35a9ebfb079de7c98c4f4d7c6df.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint a99c35304a5bc6b6fce077ff57474173db96c655e1ebb4ca25a89f3f9835b178.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 6]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 11 1, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 1, .gapLower 1 3, .triangle 4 2]

-- Cycle fingerprint aa158225cdb4a78d84c3bdf9a6ee5b200a054da9d17f3ec1820660ab78e71008.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint ab656db88cabfdb807624b02d04a6cd558b723cbf91ae0e0289e84eddf86f27a.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint abc5ec9299306bf114e86669cfd136254219edcdb924ce3125636cd81090ae06.
def localCycle00119 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint abde1cd304a054bf2350426d37d77dd8492f7beb92bc8691be81b126d8cb21a8.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint ac5853d4f673f27035138f76f99e36c60e1b4f06ed83f86c242ac363f122375d.
def localCycle00121 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 3 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint ad0c51b9613a35e961c388c168c29e46ac2da480b29658e3c93ffdcb7fce2acf.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint adf3fc1984556dd490c91e6e7f1c9e9c63c8f81dea8b3ef384f39583a15e64cb.
def localCycle00123 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint aefcbe84540611216a7c67e799f1ec74c9390e6bcee47827693382d73455bc3b.
def localCycle00124 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 4, .distance 1 5]
    constant := ![2, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 21 0, .gapLower 1 3, .triangle 22 2]

-- Cycle fingerprint af5a676ca1cd72d980e4b4da0513de139b474feb266d98676fb324d78effb52f.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 4]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 2 2]

-- Cycle fingerprint afb1a1c4265374d1a83624d2e22e6f4d9f470f61c6abb102d2d4a1cf23fff083.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 6]
    constant := ![3, 0, 0, -1, -2, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 6]

-- Cycle fingerprint b0456315827f31b39c11c1b97914acb4300f990561265081e5e055fb6bb6e1a6.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint b090db459751fc75e7889636169dca81c61f6849b5cf4d5044bacc5f120cb044.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint b23c325bbae189a17c852b7622cf69e86e17ebee59da0a29c9c9fd4190fec59b.
def localCycle00129 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint b27773c0589c7d22b0bb86b44775b428807c9d9b86d98588ba28c54bd4887488.
def localCycle00130 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 1 2, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint b45f10d9357d5e788d322faf9358b5caf19664674b8a55a6cacf2c6d083fe68a.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint b509c9c1109423ce5cad3fde9c63b2759f9d3d8d9b34747cf63142f62b17fd7c.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 20 1, .triangle 21 2, .gapLower 1 2, .triangle 2 2, .triangle 9 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint b5f4b62d9129f65ed5e262cb0cf492002a18bfbaef93d390a3f031f0bef9df64.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint b6971075c67e2e7375db3d67d45eb66d7f3b3b3e6092f561bc185e5b5d7ea98a.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint b8164e123620a5b312d263e68bb22376ab677a0ec210087c0bec8b5bf1384559.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint b86d79e41be7421e9e2ad9813e5eaf0137ef0b8436b149f71e498c003dcbc0a1.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint bb9426ff855516e5d7019c90c8cfc0502d9063829639f2e307c05d433b01a20f.
def localCycle00137 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint bba29d9fcda91bfe47770bc4cf4cb8264d644e00b64e57c2f4a41ac42b4bc67f.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint beac32d9aa135a9b75bad75fc4f6562f705019171ab5aa514311c20b83b32cc9.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint c306e12391b239c0d85bd66778195ec6bf90d3222d6408dfd21e7aca18366f0f.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 21 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint c34367650dc118023801000deedd12185d89ef9b026e0b162c79f4ecf92bd2ef.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 3, .distance 3 5, .distance 3 4]
    constant := ![-1, -1, 3, 0, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 1 2, .triangle 10 0, .triangle 31 1]

-- Cycle fingerprint c5030956040f5fd5cf30d0e6f9b5da1a1764ec093cc45e410614add47e8ee313.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 1 2]

-- Cycle fingerprint c54ea293fbbe92ea08432f26ce3b355aa091eb9dcc467a5bfaab89886d10e51e.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 0, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Cycle fingerprint c87be0a65f28cc6af32fee5dba91d9c9c7b120b3a58ecdff1e4b0c261feed675.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint c891c0f88dfadb39f9594bf171725198a3e3aed90ecc2fa347e25990c63c3742.
def localCycle00145 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 5 5, .triangle 34 2, .triangle 23 0, .gapLower 1 2]

-- Cycle fingerprint cfe332e8e198b23e876fc71e422f692bf21e1493676af1193a7e494973908917.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-3, 0, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 2, .triangle 10 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint d090395b82f65f5a1ab9820ea45de5e5cc2e9df970d94854ce3031973d6d7caa.
def localCycle00147 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4]
    constant := ![-1, -1, 3, 0, -2, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 4 2, .triangle 11 1, .triangle 9 0]

-- Cycle fingerprint d53161dcf48a9fc6a8834381f9be3f3b2f64dc2d205d25946c3908149d939698.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 5 6, .distance 2 5, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, 0, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 33 1, .triangle 30 0, .gapLower 5 0, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint d644bd84ea23d808d21b95eccb40f11d0b1bc8680f4f9052e5e1a2357dadf6bf.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 1 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 2, .gapLower 1 4, .triangle 1 2, .triangle 11 0, .triangle 32 1, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint d6e72664e451a0bef982380cb4be222673cc3ecbe124d873c8aef9f2aea2227b.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![0, 0, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint d8237aeaf0780d8491bf7ece781ca9b8c6918ca23ff7b475f685920a2b59ec01.
def localCycle00151 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint d8e66f7d8ca9801a04d193037dc9ebccc5cac4751be476859c4fdaf905aa6870.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint d8ee8bf85f4a5a76cb59ced6841dfec0ae8147aeb6121e343d3bd8e4c83578e6.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 7 2, .triangle 10 1]

-- Cycle fingerprint da6e787550d972cd0fd385400e9b04af56caf74e854febaeadb848c55ad8a1c5.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 4, .theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 0 5, .distance 5 6]
    constant := ![-1, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 4, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 14 0]

-- Cycle fingerprint db7bfb6f9688d879fa2d223d164396fd31a4f81c94abec95486d03fc66fd036c.
def localCycle00155 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 0 2, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, 0, -1, -1, -1, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 0 2, .triangle 7 0, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0]

-- Cycle fingerprint dd5a7219503d826f7b36693be4a7e5c15d9247453c28794a6bf896de133c8708.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, 0, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint ddd983fbfdb852a6427d2a2718f7dc2a5ed05a30f7274cdc03ac888bd4740c53.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 17 2, .triangle 20 1, .gapLower 1 3, .triangle 4 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint e0ccc6e731254aa266d485e4d5da684e193b93b08d2d3ab7936e4eb9fc7a1bc9.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 4, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 4]
    constant := ![0, -1, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 9 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 2 2]

-- Cycle fingerprint e27047842767959bdfad06219fc6ffec921e93c2b1ecef9134f455cb5908e9aa.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint e37296b2a682f9f59530ca202e0bd159617c651b075070857bb8aca8e865b3bd.
def localCycle00160 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint e3d3853b62d0c186e216f2129623e66bffc9485170d3e1a8cffaed8f565539d6.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint e4164260ce9232b7389bcf6779680f9e1d833f1199711be346d821da06419e86.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint e7269ed79f039a0a62d15eeed3c0e7435862440808c6d7aa05489d2d59322a15.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .corridorLower 3 5]

-- Cycle fingerprint e94d04ac88e93a2c9bca95b0727d5bbd2b06330e86a143a6608280c946eff5e0.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint ebd5648100c150d3e5e8bca94378a321ac24c566fbeb5bbb04967281a1ae15de.
def localCycle00165 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![-3, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0]

-- Cycle fingerprint ec22097ee5d5ea363e4951f39100a2763eb3e18da27fbd85b1c45664f8134f78.
def localCycle00166 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint ee7eebe612db5063371b2a13181260024a0acfab72605152a4c6b7d107cc63bc.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 5, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, true, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 18 2, .triangle 21 1, .gapLower 1 3, .triangle 3 2, .triangle 10 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint ef29ac7938489fe4895ba8a340fea1c75e20f2e71e02b038d2fc00a22e01fb8f.
def localCycle00168 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 5]
    constant := ![0, -1, -1, 3, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 25 0, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 10 0]

-- Cycle fingerprint ef3b52c5e73c788641f406617334523992ffc63afb45056f9ce80c48f7c4f814.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint f04f61890bf2990d89e72b5117b836de9a9ecc7065fa2f69e2314e5902195936.
def localCycle00170 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint f202f338a3e39f49636c5c1688bda59ad8cc3a9c24d73120986d4748008d50f1.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 2, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint f644b699db292e6a81fa426898f805ffd0f9eb10c9200944fb157f12a5c418f2.
def localCycle00172 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint f916cc537e4bca96fac2ab6c97a7fad1bdb2d3abeef208ecded2ac621ecb7b35.
def localCycle00173 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint fb6ed65b1e6e9345ea9c3b69d7204d3684d762083cdc93d652c2a272aa16fd4b.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 23 1, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint fd697b713e29944c15fe59250c3288c096b2bf73f6a8a45f59a62a7455e4ef72.
def localCycle00175 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint fdc16dc22f582408ec90c34ba0075e26e64b2df08e5afb3d1d4745ec8dd043e9.
def localCycle00176 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint ff97761e3e57c1de440c40dce3ac6dc0fc5aea0a7b1114547f25013f216c8a88.
def localCycle00177 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .distance 1 2, .distance 1 5, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 10 1]

def library : Library := fun id => if id < 89 then (if id < 44 then (if id < 22 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 16 then (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)))) else (if id < 19 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))))) else (if id < 33 then (if id < 27 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))) else (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))) else (if id < 38 then (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)))) else (if id < 41 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))))))) else (if id < 66 then (if id < 55 then (if id < 49 then (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)))) else (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))))) else (if id < 60 then (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)))) else (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)))))) else (if id < 77 then (if id < 71 then (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))) else (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))))) else (if id < 83 then (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)))) else (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))))))) else (if id < 133 then (if id < 111 then (if id < 100 then (if id < 94 then (if id < 91 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))))) else (if id < 105 then (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))) else (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))))) else (if id < 122 then (if id < 116 then (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)))) else (if id < 119 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))))) else (if id < 127 then (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))) else (if id < 130 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none))))))) else (if id < 155 then (if id < 144 then (if id < 138 then (if id < 135 then (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)))) else (if id < 141 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))))) else (if id < 149 then (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))) else (if id < 152 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none))) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)))))) else (if id < 166 then (if id < 160 then (if id < 157 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)))) else (if id < 163 then (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none))) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none))))) else (if id < 172 then (if id < 169 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none))) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)))) else (if id < 175 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none))) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 6, 3, 5, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 0, 5, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 2, 0, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 3 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6400)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 4, 1, 6], ![2, 5, 0, 3, 1, 6], ![2, 4, 3, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 64 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6401)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![2, 5, 0, 3, 1, 6], ![2, 4, 3, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 159 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6402)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 3, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 113 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6403)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 3, 0, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 137 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6404)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![2, 5, 0, 3, 6, 1], ![2, 4, 3, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 68 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6405)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 3, 1], ![2, 4, 3, 0, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 151 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6406)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 3, 0, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 106 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6407)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 3, 0, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 151 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6408)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 50 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6409)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 3, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 50 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6410)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 3, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 91 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6411)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 0, 4, 1], ![2, 5, 6, 0, 3, 1], ![2, 4, 6, 3, 0, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 136 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6412)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 0, 4, 1], ![2, 6, 5, 0, 3, 1], ![2, 6, 4, 3, 0, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 89 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6413)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 5, 0, 4, 1], ![2, 6, 5, 0, 3, 1], ![6, 2, 4, 3, 0, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 99 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6414)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 5, 0, 4, 1], ![6, 2, 5, 0, 3, 1], ![6, 2, 4, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 58 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6415)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 5, 0, 4, 1], ![6, 2, 5, 0, 3, 1], ![6, 2, 4, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 160 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6416)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 2, 3, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 64 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6417)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![5, 2, 0, 3, 1, 6], ![4, 2, 3, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 159 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6418)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 2, 3, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 113 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6419)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 2, 3, 0, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 137 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6420)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 3, 0, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 114 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6421)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 3, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 106 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6422)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 2, 3, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 68 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6423)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 2, 3, 0, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 151 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6424)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 3, 0, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 151 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6425)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 0, 6, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 3, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 151 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6426)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 110 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6427)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 3, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 110 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6428)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 3, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 91 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6429)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 5, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 2, 6, 3, 0, 1], ![2, 4, 5, 3, 0, 1]], proof := .tail 133 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6430)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 50 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6431)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 50 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6432)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 3, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 91 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6433)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 5, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 2, 6, 3, 0, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 133 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6434)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 77 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6435)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 0, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 99 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6436)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 4 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6437)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 0, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 160 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6438)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 3, 6, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 4, 1, 6], ![5, 2, 0, 3, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6439)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 4, 6, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 4, 6, 1], ![5, 2, 0, 3, 1, 6], ![4, 3, 2, 0, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 22 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6440)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 3, 2, 0, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 39 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6441)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 3, 2, 0, 1, 6], ![2, 0, 4, 3, 1, 5]], proof := .tail 66 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6442)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 3, 2, 0, 1, 6], ![2, 4, 0, 3, 1, 5]], proof := .tail 66 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6443)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 33 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6444)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 4, 6, 1], ![5, 2, 0, 3, 6, 1], ![4, 3, 2, 0, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 163 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6445)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 5, 3, 4, 6, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 2, 0, 6, 3, 1], ![4, 3, 2, 0, 6, 1], ![2, 0, 4, 3, 5, 1]], proof := .tail 66 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6446)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 3, 2, 0, 6, 1], ![2, 4, 0, 3, 5, 1]], proof := .tail 66 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6447)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 5, 3, 6, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 0, 6, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 33 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6448)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 3, 2, 0, 1, 6], ![2, 4, 3, 0, 1, 5]], proof := .tail 128 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6449)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 3, 2, 0, 6, 1], ![2, 4, 3, 0, 5, 1]], proof := .tail 128 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6450)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 2, 6, 0, 3, 1], ![4, 3, 2, 6, 0, 1], ![2, 4, 3, 5, 0, 1]], proof := .tail 1 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6451)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 128 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6452)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 128 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6453)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 138 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6454)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 5, 6, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 74 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6455)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 5, 6, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 74 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6456)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 164 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6457)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 14 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6458)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 0, 4, 1], ![5, 6, 2, 0, 3, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 95 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6459)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 6, 5, 3, 4, 2], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 0, 4, 1], ![6, 5, 2, 0, 3, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 80 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6460)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 5, 6], ![2, 0, 1, 3, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 162 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6461)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 6, 5], ![2, 0, 1, 3, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 12 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6462)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![2, 0, 1, 6, 3, 4], ![2, 0, 1, 5, 3, 4]], proof := .tail 105 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6463)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 3, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 1, 3, 4]], proof := .tail 13 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6464)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 1, 3, 4]], proof := .low (![165, 62, 79, 60, 87, 52, 59, 35, 90, 86, 147, 81, 69, 170, 86, 147, 81, 112, 54, 29, 20, 170, 53, 142, 120, 94, 41, 154]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6465)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low (![165, 62, 79, 60, 87, 0, 59, 35, 90, 86, 147, 156, 69, 170, 86, 147, 156, 112, 54, 29, 20, 170, 53, 142, 120, 94, 41, 96]) }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6466)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 3, 1, 4]], proof := .tail 21 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6467)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 3, 1, 4]], proof := .tail 21 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6468)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 21 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6469)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![2, 0, 6, 1, 3, 4], ![2, 0, 5, 3, 4, 1]], proof := .tail 5 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6470)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 0, 3, 4, 1]], proof := .tail 5 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6471)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 5 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6472)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 1, 6, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 0, 1, 4]], proof := .low (![70, 2, 76, 51, 92, 146, 153, 109, 72, 174, 71, 45, 69, 47, 148, 71, 45, 63, 65, 97, 132, 44, 46, 116, 157, 27, 149, 177]) }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6473)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 6, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 0, 4, 1]], proof := .tail 175 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6474)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 6, 0, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 3, 4, 0, 1]], proof := .tail 88 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6475)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 0, 1, 5], ![2, 6, 3, 0, 1, 5], ![2, 6, 0, 1, 3, 4], ![2, 5, 4, 3, 0, 1]], proof := .tail 84 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6476)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 1, 6, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 0, 1, 4]], proof := .low (![70, 2, 76, 107, 92, 146, 153, 109, 72, 174, 71, 45, 69, 47, 9, 71, 45, 155, 65, 97, 132, 44, 46, 116, 157, 27, 149, 177]) }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6477)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 0, 6, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 175 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6478)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 1, 5], ![2, 3, 6, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 88 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6479)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 0, 1, 5], ![2, 6, 3, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 102 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6480)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 0, 1, 5], ![6, 2, 3, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 171 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6481)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 0, 1, 5], ![6, 2, 3, 0, 1, 5], ![6, 2, 0, 1, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 98 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6482)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 123 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6483)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 78 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6484)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 1, 5, 6], ![2, 0, 3, 1, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 134 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6485)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 1, 6, 5], ![2, 0, 3, 1, 6, 4], ![2, 0, 3, 1, 5, 4]], proof := .tail 108 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6486)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 1, 6, 5], ![2, 0, 3, 6, 1, 4], ![2, 0, 3, 5, 1, 4]], proof := .tail 57 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6487)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 1, 6, 5], ![2, 0, 6, 3, 1, 4], ![2, 0, 5, 3, 1, 4]], proof := .tail 93 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6488)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 1, 6, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 0, 3, 1, 4]], proof := .tail 67 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6489)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 1, 6, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 67 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6490)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 6, 1, 5], ![2, 0, 3, 6, 1, 4], ![2, 0, 3, 5, 4, 1]], proof := .tail 176 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6491)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 1, 5], ![2, 0, 6, 3, 1, 4], ![2, 0, 5, 3, 4, 1]], proof := .tail 93 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6492)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 0, 3, 4, 1]], proof := .tail 5 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6493)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 5 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6494)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 1, 6, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 3, 0, 1, 4]], proof := .tail 111 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6495)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 6, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 3, 0, 4, 1]], proof := .tail 111 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6496)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 6, 0, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 3, 4, 0, 1]], proof := .tail 122 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6497)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 0, 5, 1], ![2, 6, 3, 0, 1, 5], ![2, 6, 0, 3, 1, 4], ![2, 5, 4, 3, 0, 1]], proof := .tail 26 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6498)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 4, 6, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 1, 6, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 111 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6499)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 6, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 3, 0, 4, 1]], proof := .tail 111 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6500)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 6, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 3, 4, 0, 1]], proof := .tail 122 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6501)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 0, 5, 1], ![2, 6, 3, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 143 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6502)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 0, 5, 1], ![6, 2, 3, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 6 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6503)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 4, 5, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 0, 5, 1], ![6, 2, 3, 0, 1, 5], ![6, 2, 0, 3, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 104 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6504)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 1, 6], ![2, 3, 0, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 40 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6505)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 5, 4, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 5, 1, 6], ![2, 0, 3, 4, 1, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 40 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6506)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 5, 6, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 5, 6, 1], ![2, 0, 3, 4, 1, 6], ![2, 0, 3, 4, 1, 5]], proof := .tail 139 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6507)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 5, 6, 1], ![2, 0, 3, 4, 6, 1], ![2, 0, 3, 4, 5, 1]], proof := .tail 172 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6508)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 5, 6, 1], ![2, 3, 0, 6, 5, 1], ![2, 0, 3, 6, 4, 1], ![2, 0, 3, 5, 4, 1]], proof := .tail 129 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6509)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 4, 3, 5, 6, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 5, 1], ![2, 0, 6, 3, 4, 1], ![2, 0, 5, 3, 4, 1]], proof := .tail 166 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6510)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 0, 3, 4, 1]], proof := .tail 117 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6511)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 4, 3, 6, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 0, 6, 5, 1], ![2, 3, 0, 6, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 0, 3, 4, 1]], proof := .tail 117 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6512)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 6, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 3, 0, 4, 1]], proof := .tail 152 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6513)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 4, 6, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 0, 6, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 3, 0, 4, 1]], proof := .tail 152 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6514)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 6, 0, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 3, 4, 0, 1]], proof := .tail 8 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6515)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 0, 5, 1], ![2, 6, 3, 0, 5, 1], ![2, 6, 0, 3, 4, 1], ![2, 5, 4, 3, 0, 1]], proof := .tail 37 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6516)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 0, 5, 1], ![2, 3, 6, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 3, 4, 0, 1]], proof := .tail 8 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6517)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 0, 5, 1], ![2, 6, 3, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 2, 4, 3, 0, 1]], proof := .tail 73 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6518)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 0, 5, 1], ![6, 2, 3, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 131 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6519)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 6, 4, 3, 5, 2], ![0, 6, 5, 4, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 0, 5, 1], ![6, 2, 3, 0, 5, 1], ![6, 2, 0, 3, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 161 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6520)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![30, 119, 19, 82, 121, 38, 59, 75, 7, 10, 141, 168, 69, 28, 34, 141, 168, 135, 126, 48, 158, 101, 36, 103, 167, 61, 49, 24]) }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6521)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 4], ![2, 0, 1, 3, 5, 4]], proof := .tail 130 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6522)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 0, 5, 1, 6], ![2, 3, 0, 4, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 144 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6523)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 5, 0, 1, 6], ![2, 3, 4, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 118 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6524)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 0, 1, 6], ![2, 5, 3, 0, 1, 6], ![2, 4, 3, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 56 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6525)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 0, 1, 6], ![5, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 6], ![2, 0, 1, 3, 4, 5]], proof := .low (![150, 173, 23, 15, 18, 127, 59, 25, 169, 140, 11, 100, 69, 43, 124, 11, 100, 55, 17, 11, 85, 145, 11, 125, 83, 115, 16, 42]) }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6526)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 4, 5, 3, 6, 2], ![0, 4, 5, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 0, 1, 5, 6], ![2, 3, 0, 1, 4, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 32 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 6527)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (6400 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 6400 ≤ id.val) (hhigh : id.val < 6528) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 6400)) = true := by
  let j : Fin 128 := ⟨id.val - 6400, by omega⟩
  have hsum : 6400 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (6400 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard050
