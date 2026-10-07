import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard041
open N4R2OuterLeftReplay

-- Cycle fingerprint 0158166f80d85369570afd50872a03feaa3763aa1ce05ecae4231d8beeaf09ff.
def localCycle00000 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 4, .gapUpper 3 5, .gapLower 5 4, .triangle 17 0]

-- Cycle fingerprint 0219593d6c93a73f2010e4033267855018759923c1cf60fefd0cd95916414c24.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2]
    constant := ![-1, 0, -1, 0, 0, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .gapLower 6 4, .triangle 8 0]

-- Cycle fingerprint 02382f3855d0d27640a1dba9a60bb8c43325e5d889eb2d933113d9da3e18f2d4.
def localCycle00002 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 02cc17b4640e5b4a84cc239db679f25603499f6f9cd9272e063691b3c714e981.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, 0, 0, 0, -3, 0, -1, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint 034203772c447a0753e7ec3a25be553dc1fb26ab60632806d729095e196ea304.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 04e1425e839f75f4da483f3e4ccaacc45ec80562e3eb1778462b0754d5509edd.
def localCycle00005 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, 0, -1, -1, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 06b74f9ff4c985cd7d77bdc6dd229f38f536a51dddbb534a0ac2133ca4796fec.
def localCycle00006 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 27 2, .triangle 18 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 07239b41f502a2508c67a91d8103ee8bc8b0f3644a659d18c559adeb73b99703.
def localCycle00007 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 0736865572877d720b5d48441b70cf53452191f4c90384b804e777913f015fbb.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 6, .distance 1 5, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 3 2, .triangle 7 1]

-- Cycle fingerprint 07b70b8a1735d39ebd416417d645ff96929f964e90170ed09131f744d5d35ec5.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 07fb70a12ea05c8e5d36033785f2160c9c0b3924b65a57dbeea157b7eb7c2b99.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 0a6c93b4e1d494985d454d9cd717a4fe7b50685779942c386cba1d067865a153.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 0ad19470ecc086d1f07df4c418ab98ad91ee59178a11a94da91138aff2dc69a1.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint 0b40a28bb203d5c38cd113add61c999826f120bade68b7bc19c11472c1f16784.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .theta 2, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![-1, -1, 4, -1, -2, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 25 0, .corridorLower 2 3, .gapLower 2 6, .triangle 17 0, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint 0b790ed299eecfbb41c70b20c5c0d995e95ecb224a5ab5d200b099f012e87fed.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0be961b25cc229563c6cba0056560d1842fcb7bc0b385d13f18362d915b703a1.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0c8183a822b0d6057f85bf362ce24115c4b2759c78ff6dfef76d624ceee8522d.
def localCycle00016 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 2 6, .distance 1 6]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 16 2, .triangle 19 1, .gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3]

-- Cycle fingerprint 0d880a8b4de37d8758ec65489bfeb0938b11ee01a9746e7b257d1b3b3fe400ab.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 30 0, .gapLower 2 1, .gapLower 3 0]

-- Cycle fingerprint 0e546a8dfd4303894170b4c521a45de2c7986aa9814f243529d56a5939a496a8.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 0ec1416dd810a8d4148460c483469f9a15cbd1588d1abcaf191db0156a4b24f0.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 0f5fcef2b04e9a002165f514b7b9ede0b9c7b53340efe54764206fe3f7ec1b7e.
def localCycle00020 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 10cd44cd69dce836c954ddcd43d2e6cd44519bf66564b5b68f6c8037cf5db02a.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 1116645633dd26963bd9770d3fa368f6b6ca9b5de5c38042e02672dd8097b585.
def localCycle00022 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 12f4d76b21c88fbac0f2d84efa3249eaaa2e9dc9466ceb3c3cc0718e7b9a7c71.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 130b283b45fb04b8ad615da8ae0b862497d48984195cb317b517dcaea10135bf.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 17 0, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 132d25a7b085e51256dd11cbebec49088b948a11c7ef59aa945ee9e15b7c4fed.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1546a9a38150f9a763cda117ff804c922898917a226ba06532d6037d68eb6bb6.
def localCycle00026 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 154cc6c1d9ee5b3a3ec855178f91ef67e0f4b0abb6d6e73d69d22c736cb25e2b.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 16309bb4a0f0c6f60c9a820be19766499806fdcb594df602ae005bf339c44748.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 169f88ba49cdde684c73cb6fb28cb84c2d11e18e235bd8e5bb44fccb8f35dded.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 2 5, .distance 1 5]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 16 2, .triangle 19 1, .gapUpper 3 3, .gapLower 5 4, .gapLower 5 3, .gapLower 5 2]

-- Cycle fingerprint 16c0fa9344573e1ab6e43ad76b560ddff244b76904b78e7382d1a43438a9f23b.
def localCycle00030 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 17f30cd3f5e6ba09d73e813dbf50c3d8002a4aa2e0d60754d93034c96ec58aba.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 1801a03915cd8de8c11642cc1622111001616ac1f8f8eab8ae50f1642f5f30d9.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 18b0baeeb6749f12b17ddab2d3dc3c66eeb599aeb2fb815bd8b8b45365b5fff8.
def localCycle00033 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 4 0]

-- Cycle fingerprint 1994a9c643d55d115f8638d1c204069d65d5ca2218394e0972d519d6894f7fee.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 1c11951181a67e67d62994a17b7e94d7e512ac96857d81dbebc49cdfd5a89b8e.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, -1, 0, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 20 1]

-- Cycle fingerprint 1fd9650831b023a8ddc77a038dccec0cbc0f7981958a08f26b0e240a0cecc349.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .gapLower 3 0]

-- Cycle fingerprint 240063ee855dd3dfe487d8debcb1797461acded74ec4f3d7681ff597fa9dddb6.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 25562e6a8b8abddb2e45c358ea004c79b7db911bf2ee216912d0a7f8686ae6de.
def localCycle00038 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 25a52b8bd6d9cc83423e146b2ff0882e44527d272a6b09ba73f2abf11912cbe2.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 20 1, .gapLower 1 3, .triangle 21 1, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 2644e7783b76175a086e4c625969e86987be9d60692100a60a5375620b0977bd.
def localCycle00040 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 4, .gapUpper 2 4, .gapLower 6 3, .triangle 24 0]

-- Cycle fingerprint 27ea50a42eea6622d9dd662a3f610f2a37e7471ab41cb6214a7d1f90f298d658.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3]
    constant := ![-1, 0, 0, 3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .gapLower 0 4, .triangle 6 0, .triangle 25 1]

-- Cycle fingerprint 280c9d76d79f2fde676491e3421113cfa2ceb8b6485a208fff994a5f529a9396.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 18 2, .triangle 21 1]

-- Cycle fingerprint 28846befb3ba2481b62a18517227615f1b2d3d717b900e1f3e4df91ec768f476.
def localCycle00043 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, 0, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 28c3ace43d7a0ed73ca041bdf379b33f4a66b24dc84def3aa20158434bc7e107.
def localCycle00044 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 2 5, .distance 1 2]
    constant := ![-2, -2, -1, -1, -1, 4, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .gapLower 2 6, .triangle 17 0]

-- Cycle fingerprint 2a6f1af29f74584ce6249d28e4707e25bde9c3e37fb5af8734533da4118e55cf.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![-1, -2, 0, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.triangle 17 0, .gapLower 1 4, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 2a769381f865c7b40c79b3abc5223bccf5774647f7bd5d190778f671384e9b02.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint 2ce87b05c0b613483adeed715c9c1a58714169a3049c1a1baede9070f74a9148.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2d2f12c3ffbfc84ed28506b06833d8afda9cb66250f190d96c39f668c1029b58.
def localCycle00048 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 5 4, .triangle 17 2, .gapLower 1 5, .triangle 15 2]

-- Cycle fingerprint 2e8f398aab2c5a3e40072c54affdecada3dfc33d6a2dcca187acbf1b253ee941.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2f62a579441646bdb35cae7039bc16af3cb1e49528a465d7500b7343a74a8ed9.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 2fc33745a0d560fba93350e1715f257c762b8cf0ecb1c103888368ea13ceb71c.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 3, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![0, -2, 0, -2, 0, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 1 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 3113d54aaa6f1e45535341aaff84b81296d0cfba541b12d483a75841c6b08fe1.
def localCycle00052 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 31b1502d7a66f0ed8e930d887d4ab6a14d368b47cda5c1778e4e1e243961e6bb.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 32922ddff6dfb28df102a248101fbd9dfa3c9bb294d5ee841db47daedaeb3bcf.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 32 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 15 2, .triangle 21 0]

-- Cycle fingerprint 335703df196b5cd09b3059340de6268412162405be28b3ca704b178962a5bea2.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 34c226bfaaad593d260a4e83cf5dd9ba3c091fcb64943586233fc63455374722.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint 361f39f8c9b5b834735b5ff9ccef2acfbd8fc44b691cd80bffa933d5fdb2b607.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 3686c051613df8f7819c3342c74bae231bbd9d30b8c9746f70c82f9b953c4e58.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 368fe4904b12f2c71a6da6e7290f87bf0d6cfc4922540e7ee96a7b905a0a61d6.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.triangle 32 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .gapLower 1 4, .triangle 21 0]

-- Cycle fingerprint 36acfbdc60e68a17e6206585bd0074b9db8cebafd709a3106a09238a6cb83327.
def localCycle00060 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 3847dcb0bd4e234b4ca8da20d92acabf1b2373a253c40f72fda4713097616447.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, -1, 0, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 14 0, .gapLower 0 4]

-- Cycle fingerprint 38d8edd14eae1ad97af3c65f95e6207bf5628f0ac29b90f3f6b6d3b4322fbf86.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 38f93bc1d7bbc085c928c1183bb8eaaad79838a89b95968320d867078e7e587c.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 15 2, .triangle 19 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 6 3]

-- Cycle fingerprint 3a18b8b65be2b0655f33d6d6fab02c4ac489fc1b7cdbb836456b66c5cd97424c.
def localCycle00064 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 3ac10ac919e4c7cd128844d3f62c602e8c9a5bdaddcaee9478a03f7f8b657c30.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 2, .triangle 19 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 2]

-- Cycle fingerprint 3c15984d040555395ba67e4a69532d0c78871076887ab82a1af3572e56c4b680.
def localCycle00066 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 3c69647f8138deb8d0e712908df4f6631db751a49ee01e7659eb8ed9c55fb0eb.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 3d3b7be79afaacfa2e5d2f1d62911cfd9b4aa46a04bb8439efb8fcca8d274fa0.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6]
    constant := ![-1, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2]

-- Cycle fingerprint 417ec55c93656d925d87943ceda542c1e4eee861983dc21a865a85d038b5484f.
def localCycle00069 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 430b91a3a77e1b6563c5e5fa1a3d9fb6cca024e1520ce76ba84e35745f1442d4.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .distance 2 5]
    constant := ![0, -2, -2, 0, 0, -1, -1, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .gapLower 2 6]

-- Cycle fingerprint 431f0f152a995af9b5761718a21f9d740fa06b1e0a66f709c1997cdc59e0834f.
def localCycle00071 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 4417220018074cc2f6afa0cb9edc6936700cb242644e572bcc1bb7ccb6542748.
def localCycle00072 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 445eb8b8c3ee3f7ad58875c5b4c53d563ae81ce85fd74d681ddc0fee3e655fcd.
def localCycle00073 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 46045d2fea693f3a5d0c00c54a2fe0cded58be729706c07eb484e2c8771b868c.
def localCycle00074 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 5 4, .gapLower 5 3, .gapLower 1 5, .triangle 15 2]

-- Cycle fingerprint 479a2a4240b54ba514f6e1f1832ba681a94e3b068cd9449c7f6ad2f536271a29.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint 4955628f6642f16f031ae1bba86db35f1559f3be3f95e1407d8c4df60b4b1810.
def localCycle00076 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 49604ae724244e36086e6b9e9bba41cf30afb0e72a85aa119cbb7225d906314f.
def localCycle00077 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .gapLower 6 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 4a7d1820dc24f6c7a5454b39ca355b717babb29614483cb253a0cc718820b3e4.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 4a9a4fc2fbd2092af3bf69808d068e3a22199cfd0eecbb879aa32a79c17e2ed1.
def localCycle00079 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .gapLower 5 3, .triangle 17 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 4b45c1e48281d4a825c1e86683c9ae925ded994d7fe482c6df2e159dcd6031da.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 4ba9575e8ca722304744cd6f685006e132d0d1d773c752b03096f9988955a5fc.
def localCycle00081 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6]
    constant := ![0, 0, 0, -1, 3, 0, 0, -1, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true, true, false, false] }
  origin := ![.triangle 4 2, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4]

-- Cycle fingerprint 4cfdc45027721f53a77019183a87f42e3037616e39245b041e15e2f4398f8591.
def localCycle00082 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .triangle 16 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 4d3c97b5452523191ddb8cd02ced549ccef4d7fbb68b2ad08212a5ce250474bc.
def localCycle00083 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 5 4, .triangle 22 0]

-- Cycle fingerprint 4df5e838e45ac16a7c1e423709ffd914c45b9c004c172f49e5f9a0e7c685d319.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 4e15553d791b78dcfde12ecbd58057e1319c417945ca4c8007bc5ec438f3a641.
def localCycle00085 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 4e95d6450bad7c6699a2d6933d5d208a3758332be493a6d3aa487f6d097727db.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 4f68588fd573d426c8f8cc7766f2350f95251c5e481a21e1e1cbf1856eb28882.
def localCycle00087 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .triangle 21 1, .triangle 19 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 4f8acfa14d955e5942d11f1376e1d44c792e64eaa62c2bdc8d9366542c293deb.
def localCycle00088 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 14 0, .triangle 7 1, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 50417e833c2d024b3722cdb8509648e5d14a3a87df75849c00c9a75c6fe0527d.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 18 2, .gapLower 1 4, .triangle 0 0]

-- Cycle fingerprint 5222c12010a7cb18308e6d25ad72b63cd450be3325d7d11294eb56b8e3524172.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 5256178286a7f1858c8aba18a0cb07c6aed1e7e79ac8e750cbb9ee1e8be02a94.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, -1, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 53c083aed503d7fe9a4cc4d2010892ee4c04addae3a2b2f70b9b4a33d4eda225.
def localCycle00092 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 3 5, .gapLower 5 4, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 54ba7fa52f075cf0c583f61de0b34b2f9f210a2cdb05857cc7ba3b5c6acdeda5.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -3, 0, 0, 0, -1, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 55ae4f485519d609555706de983ee37ec2ff453ea7eb87dc6c2753bf20824570.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 2, .triangle 2 0]

-- Cycle fingerprint 55c68bdbf6752cb2b06ae4283c7097ce3815b91fb23b7b46f5173b8a587550e4.
def localCycle00095 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 19 1, .triangle 1 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 5667dcbedd7fb4acde5016f49a796aa3693d8396f3cb08810c6104b7c550f541.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 581cb71c8d3eee9d57b26bd33bd39edeb4b72826506d61362c19672bdee2b9d2.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 18 2, .triangle 21 1]

-- Cycle fingerprint 58a3c266584270148253fb60d2c09fbca6c25a98ae8542d8ebc8ad4eb36cfc8a.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4]
    constant := ![0, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 5989a94c01118eccc4dfc095fcb449ea2b0829adee6d2f5515a145ae7a962a1f.
def localCycle00099 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 5afc8390387a33d6ab4640d3dbd713ba6f7e2c03bc6886664835381ac83079f4.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 5c3c5046ca8f34d85c2838acbd66f780304560e58a3c43d9f340c7b4146e70c4.
def localCycle00101 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 20 1]

-- Cycle fingerprint 5ca896964e3f70182a9cd49811c227b10757cdb8ef8c4bac93f74f526a87c906.
def localCycle00102 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5cdeec6d2eda5ac458aa5cee8f936e7dc3340bb10241c9842ae8d745177ee2c1.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, -1, 0, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true] }
  origin := ![.triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 4 2, .triangle 14 1, .triangle 7 1]

-- Cycle fingerprint 5f055df220486dca883eccf02019f48ce0078a11e2363b301c4a5519038d7439.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 5f8df11d977cc72c31835eaaa5dbd97e207e6a9123381f99fd08f316454b9bd4.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 4, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6]
    constant := ![0, -2, -2, 0, -1, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 6 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3]

-- Cycle fingerprint 5fc82cf3035821310da556ce409cff0c5b430c937d8bce2da0266d491d4f89ae.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, 0, 0, -1, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, true, true, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 21 1, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 6127bf8e17c7aff901126dd5f487416b0f8735eb20d782f1584b82709f33347a.
def localCycle00107 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 615b98dec0981dc9050ec195eefe431154ba8bdcd4a8962cda46769ae1242899.
def localCycle00108 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 6230d942593691bef280046360890cd1c7d369ea0b4e43fbc53264f94d3f49b2.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6]
    constant := ![-1, -1, 0, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint 62c5d06d0de711e378af8c772fcbd498191b37089f6f0b36525a028215aa2404.
def localCycle00110 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3, .distance 1 6, .distance 0 6, .distance 2 6]
    constant := ![0, -1, 3, 0, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, true, false, true, false, true, true] }
  origin := ![.triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 15 2, .gapLower 1 3, .triangle 4 2, .triangle 8 1]

-- Cycle fingerprint 6442a6ca3f572a806b40f2cb9946ee09dec89fce69383d78201fe08e9875e5cc.
def localCycle00111 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -3, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 2, .triangle 11 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 6596c70c7ddf6c5d6b209ab3b3bcb857f56845f304f4d13fa7bd1ad79c2e54b7.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 67b9e8281326d6aaaf7e1b3d0aee7d6e518ebb44f2e2b289671765b5f8fec61f.
def localCycle00113 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![0, 2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false] }
  origin := ![.triangle 19 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 6a68d2bb8170eb3ccbae72bbfc914e8c2be68252de9fd1cd1b72a33dee4eeaa0.
def localCycle00114 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 6af7b7814e38305765c6ccf6f8c2dc63cc64546823dbdc654057e6e7c821cb40.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 6b69605fabcc246ae163b155be83c221f15267128605c461bb15cf223ccca896.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6ec2ce38305f05942b5c502802bc822a4776737067ab05b37337882b5a411d3b.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3]

-- Cycle fingerprint 72c0cf6e4819d3e148d4902d9be9e6f07d7b7f3da6d5ec9b15c70b2641929540.
def localCycle00118 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -1, 0, 0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 30 0, .triangle 24 0, .gapLower 1 4, .triangle 16 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 73c0eaefe946a31c429ae615f3786fb22b0c3735b159a04ab0df24a355bc7742.
def localCycle00119 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 73ce53860a792d5a9a2b470928d6941a7506a190eee3c6d9e230062dd916fc78.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, 0, 0, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, true, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 73d62679761ffd6c7339ef7f65a2b4836995ca70e4ddc66d841d4493d863cd31.
def localCycle00121 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -3, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00122 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 7730149eb2ef3300b23bc7a15d8838bf4e256e8e5db9ece57d2cf78254274467.
def localCycle00123 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint 774c55349f81aec08ea5de3e4defb74a7236b7b253b6616fe412fb6299305c1f.
def localCycle00124 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 78032883f0771bf17ed0698e46aeccaa8993c5b2232c172c22986804c6a1ab8f.
def localCycle00125 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -2, 0, 0, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 23 1, .triangle 19 1, .triangle 1 0, .gapLower 1 0]

-- Cycle fingerprint 78057289e73ce186fbc9f5ed6b3046b5987b4baac0297327cb22fd4965a3cab0.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 7824e30ecf09dc6d8574f4a8336d20de35c45d023da5f8cc9d34f59e2348f9a0.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .triangle 0 0]

-- Cycle fingerprint 7874815586de22c39c33f0013a9fffd8c6cb65dd8d414c97ff0e16db1b5367fb.
def localCycle00128 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 1 2]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 4, .gapUpper 3 5, .gapLower 5 4, .triangle 17 0]

-- Cycle fingerprint 79e0a2a11fcc18dac8bfc86b3eba9e571c7c04723955ac09acc01717630fbc34.
def localCycle00129 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 7a702622c7823b5beb8d31ba836837767257103db089e89d63d5af8443619b95.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 2, .gapLower 1 5, .triangle 23 1, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 7ac11edabceb51a6882dceb6d36755c7fc16f99cde664db324ec6a484759bc18.
def localCycle00131 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 7b573ad17422ba3bbc5cea5925673f122495deef4e8944789ce38726639ec11b.
def localCycle00132 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 4, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint 7d531947871fd86522dbbde5ae784ad947d72b08b254b89d7feb41d53ede2c60.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .gapLower 1 3, .triangle 1 2]

-- Cycle fingerprint 7d66771e837631658b1e79c3348b3dc00e20745ce5d653a81f4c5acd997423a3.
def localCycle00134 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 7f71a21734afcf5308d4646abb219f7d5c8e9bc7d3081faac1967eb7563c3cbe.
def localCycle00135 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 3, .gapLower 1 5, .gapUpper 2 5]

-- Cycle fingerprint 7fe9e006b5fd6dae75b2a2ff1fa9225f4be6b5eacaa80ae1988e735d37144b41.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -2, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 812a6e1a59ad5c69c5092f52f65912ad9707edfb7a922db1c6dfbea8e911e0bc.
def localCycle00137 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .distance 2 6, .distance 1 6]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .gapUpper 2 4, .triangle 18 2]

-- Cycle fingerprint 8146d7ab54431798493666e107b2fee3bbdd9419f1f59558b4d7c378892c9742.
def localCycle00138 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 14 0, .triangle 10 1, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 820ec20fe02ef7b2cf548062c217c44083cc09b86fec5d80cb88c5e07b5c8940.
def localCycle00139 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 82a0ffa3d9333ba70b6cd6625221c083d43f2a139b5423f1bdc46fc776c9c97c.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 83d25514645b1a16d4ee85d37c43293f2b546fa833a886a9849077e3195a9980.
def localCycle00141 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -3, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 842dd7fbc0e9b2fdaafb263455ffd671cbfb59c71a24f3bba60a3a6580b44fd0.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 8641ba6f8cc8c8b39f8cbc03c1091d0206d7e052790d33206262bf356ff24322.
def localCycle00143 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 86df220cb7807e36225862be3a00c6e7e60287fa71a67c0c8a5ba53b9c3eb41d.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 86fe160638899a31e9d9f064573d09b8f7e6f45c5d5efa13ea6089f208250674.
def localCycle00145 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 87f84aa310e6a83c946e63f6ebdb2334f44303567cd611b27d0f31bd70e5aa62.
def localCycle00146 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 882cd229e462676a20d517f8ab1afb78e706d8312ef7b76d2e86011398152fa6.
def localCycle00147 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint 88824eb050533e276747f73f89f961a7c63a52789bf6f26f5fcaa3b71546cde6.
def localCycle00148 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 89be7486d8c8e9216eaaecd4e47431c64b6d0856ad6b277e923f3826197ab310.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 8a587f70b50aab7a367bdfd1e9f51c2ffcdede6c0a450a5b5508e8cf20fbdcf4.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Cycle fingerprint 8a96b12e0ab0aafef137f0f8705272092f85130e37c93d8e7f4525034b20f6a1.
def localCycle00151 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1, .gapLower 1 3, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint 8c3d4125e499cd5be6e623198361f12de69b720d0950d6e6492e70c1c3f707c6.
def localCycle00152 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 8f00df711caf0afb2d2ed3bc65cd62c7d07a6bc4e2ec4ba5c4e430bd2f97391b.
def localCycle00153 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint 90b2ffde6f8806fa8b2b7d08bd74ebc97957307d7336676d430fc67dda6d3a3a.
def localCycle00154 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .gapLower 3 0]

-- Cycle fingerprint 9114dcf2ba44e3c43bbd85c4046dbc94b32969c6477fa8426ddd2dcfd584af4a.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint 91424af3322832163fdadc3061ca85ed65e08b051fce299e5f4904832e5601cf.
def localCycle00156 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .triangle 1 0]

-- Cycle fingerprint 9299395381ad03266d21436831ce123948d82eba42fc8bc40cf4eecbd340d23b.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 93afa2a2202edc79cfafb2eb9c5c10c1751e8d7702283fdc12a781ff10ede8f9.
def localCycle00158 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -1, -1, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 93ebf2b7c0ed2a0814fee83cb6c0c7b20995ad130fbfe96b1695261cd4fdfdff.
def localCycle00159 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 94905be2375e969d8eeac381c2cdec84a6404a7309b996310c835e7a1b740f63.
def localCycle00160 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 960a5d7fedcf3b0a0457c3b15f96aa70b5b0ace03c155fe47d9741a69f09a0e9.
def localCycle00161 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapLower 1 5, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9676f74515c09d52808d5e7cd3c96315d3baba559de3a48e0b8f89e2e7021afd.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 32 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 15 2, .triangle 21 0]

-- Cycle fingerprint 973b39efecf2047a4242802e37fe31e45adf6c84e253be2acf22a10a6410c50b.
def localCycle00163 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint 97edbfb2eda9bb29b602f8417138018995274b5a83a19a7b651b7822899323da.
def localCycle00164 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 985cd8c2f2d93e1851058bd5b16ca9e3f9909f1fa5f2b0b0d9c050fd202b0971.
def localCycle00165 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 2, .distance 2 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint 988b533cd739859b43a07dd7605702384a4a80d1e9ddfd54227e2c634b12c7bd.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .gapLower 3 0]

-- Cycle fingerprint 993c9d8548fee0c9da3097e1e6b406b85a0c6a8347593823cd42174608dc84eb.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 99d1cd70d39816b824312b490b15caa3763a5695aad5ffebc6e9298e8e3c0737.
def localCycle00168 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 23 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 9a0321078f88f666c333c4ec13afc8f4f8c1883f8343ab2250076c8ca0dfd764.
def localCycle00169 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 9a044572a58d74646974ce15ebec7e810e461f6d2c903360ace6875e9310ebb4.
def localCycle00170 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![-2, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .triangle 21 2, .gapLower 1 4, .triangle 16 2]

-- Cycle fingerprint 9acaade25cfc9283ade68ab83a3216b30909122cb4b17df9cb892a8a258b82f5.
def localCycle00171 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .triangle 16 2, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 9b3d052dcfb2bf608ebca3726da67db61792da66ddbe695ad92e78bc1033648e.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 4, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5]
    constant := ![0, -2, 0, -1, 0, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 0 2, .triangle 6 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3]

-- Cycle fingerprint 9c2398792117c9230504cd88cc96634c7aa70d930d188bb7d1e64541bd0d5a02.
def localCycle00173 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 5, .distance 1 5, .distance 1 2, .distance 1 4]
    constant := ![-2, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .triangle 20 2, .gapLower 1 4, .triangle 16 2]

-- Cycle fingerprint 9e3185304ec09b9581b66620204b1702dccdef23e44c0b0c4ccb1a31a8b844a8.
def localCycle00174 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 1 2]
    constant := ![-1, -3, 0, 0, 3, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 17 0]

-- Cycle fingerprint 9e5af5a6616ff4333ded9d1770b5acd476ea56a67f7de0cb9ab726b969056bad.
def localCycle00175 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 9fc4c1b43cb158e07fd929a293629b073b2b69dbd66a8b1256c3f8fcffb75eb3.
def localCycle00176 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 9fdeb658a4ec565c5092c259c6f7a8ea60ed6d90396821ea806da35c0c3bb3ea.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint 9fe4b280c92f24eb54e5abd7c12de2ab6544e45086b10b8680c11e7a498bd8c6.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a0a603fb73084548468b6c17d8c0bb2feee9c8ca11489541bb7f4e4e059f8b96.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint a1e82bdf8b2be7b8f35a93ced9e33a2efa967965c34fdbafab56953c0a6eba6d.
def localCycle00180 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 16 2, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint a3b917a4a99cd4666779e753d3b98a55a1ef1ab1861a5386ece6b1506f45a55e.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint a4f9e65c8eb8e762e6ac4eee539109030262bdc3552939659b3124d608a8bae7.
def localCycle00182 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapLower 1 5, .triangle 17 1, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint a5fefd5770e0f95137d74db0f9a1d2906a2767eb30143b54009f108a4a587985.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint a841107a34fda27fe2c4ee92a0c9c3c88a8726a4f018e565abcfb016c1cfcc6b.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 0, .gapLower 1 3, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint a845def362c73029eac705a408445e24060c1b43368c1a2e245a80b1777247d1.
def localCycle00185 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, -1, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint a8463b2d29969a70e14573da7f83075cdc921c1f391b1207023456aa7a3e086e.
def localCycle00186 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint a930409d953adbb1823eeda0c6dea6413b0da231debf6ec24532e345e3b22bcc.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint a9a1c5ef5da821188b017cf6379f82c1e15c339d2efa456de006f53832a95a8f.
def localCycle00188 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint aa71123a82574bbc9d0d71d3ca00641b7b947f683cf6a30e009ab0368ff78a2b.
def localCycle00189 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6]
    constant := ![0, -3, -1, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 5, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3]

-- Cycle fingerprint aa7991b4085c95ec653cee68d201bfa714dbec58a9b3532f0aa11e0c8e32428f.
def localCycle00190 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 2, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint ab118f071ac4470bbf608262e15726aa46274bda28cf691861d70322ef1c4787.
def localCycle00191 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 1, .triangle 14 0, .gapLower 0 4, .triangle 6 0, .triangle 25 1, .corridorLower 2 3]

-- Cycle fingerprint ab8e55b69d7dc9bfa6d39865ed96a42c07c4577062b64e04dcb7a99d45816478.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaNext 1, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint ac14019fb54dab02895ffc87f8393930353fc8d2485bfaf65b874799316c0419.
def localCycle00193 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, -1, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 2, .gapLower 1 5, .triangle 3 0]

-- Cycle fingerprint ad421a8cc8f1754786aed55c472cc9a83c50dc072b53d770c3cf6b6cf86db485.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -1, -3, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 1 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint ad8c3988104fbc5dd2988176e95fad4ac009031920373ed2ec748caa8a11bab3.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint add9451b575837d2f5aab1fcbc76979c8fcb807e0fc2605d0487dd9915c93fc3.
def localCycle00196 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![-2, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 1 4, .triangle 15 2]

-- Cycle fingerprint adff70e09463ded8e063af2b39330f1d87acc935de77f1aba6b129356f5fbc83.
def localCycle00197 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-1, -2, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint b090db459751fc75e7889636169dca81c61f6849b5cf4d5044bacc5f120cb044.
def localCycle00198 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint b0bb0a940ea8a0d29643b3eb467fb8a0ec8c3ca7939992ff16e5ec300bbc99e0.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, true, false] }
  origin := ![.triangle 32 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 15 2, .triangle 21 0]

-- Cycle fingerprint b0d1cbbe5c63833ab41c165222a2390d5799b9a7861f7ec6f4fdd6d662705a78.
def localCycle00200 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .triangle 23 1, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint b166e69f9c916d223b7880d4103f92b2eac9da16e38ae06efc8ebd1e4725c089.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0]

-- Cycle fingerprint b31843cd0d4223406b3ea6e191706461a5511f26371df9d03e70a9e9d3b05a09.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 0 0]

-- Cycle fingerprint b33e5f05190f931ec1d760bff36cfb73bd6ff43c9b2d7c716634bca6ac976ebf.
def localCycle00203 : Cycle where
  length := 4
  data := {
    node := ![.distance 2 6, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 3, .triangle 24 0, .gapLower 1 4, .gapUpper 2 4]

-- Cycle fingerprint b530ca181000d395fec88dbbc3238a8b014abb8ee54cbe0242bdda6ae076577c.
def localCycle00204 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 5]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 5 4, .triangle 22 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint b5f6b4461ca4055e7705988327d92280c3023bcd6010d35ee15e8a44e57ae5a3.
def localCycle00205 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 6, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b6a58d5c44dd572499f6711dc928a618e6f6c385eed4183b473ef7553a1aef59.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint b780a8257b0f3100f63cdffb4091e7c1a19e7b541a01b0cfeb4d5e81cb95da74.
def localCycle00207 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 2 5, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, 0, 4, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 19 0, .triangle 25 0, .gapLower 2 0, .gapLower 2 6, .triangle 17 0, .triangle 18 2]

-- Cycle fingerprint b7a976f034988305457f66ce6ff1959f109ee38b74d3988d99e0239393395704.
def localCycle00208 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 30 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b7b733d5acfa35b460bb6028ae3a0d6fc026c5b46e30750cbef34d000e1386be.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![-1, -3, 0, 0, 3, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 18 0]

-- Cycle fingerprint b7bdad8d10a1d1210895a0e2f25791f72df69813f2d1052ec1d2a8b1dd82ff7b.
def localCycle00210 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 5, .triangle 0 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint b7e89b51b55a4d94c31e00d8be9b33d94ec9e3b05a93c35fd2574a4cd7ed70a3.
def localCycle00211 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .gapLower 1 3, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5]

-- Cycle fingerprint b88200b16343f5746d86e44b4512d0301f82269ba351cbf30889853bc39a97af.
def localCycle00212 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint b8cdc6304422207d1c239f7ee6e32a330d63bb1b4dfbd39f4104ac24a49afb01.
def localCycle00213 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 2, .distance 1 4, .distance 0 1]
    constant := ![-2, 0, 0, 3, -1, 0, 0, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 18 0, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint ba0d83ded1e1c5c50290195697efc990bf958aca5e3db86fff69833438e10a0f.
def localCycle00214 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint bc201d90bb0f14123bdf0b383b639f3623892a6c741e4562bef3f460c7846529.
def localCycle00215 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint bd8c05eee1e8e45bcb1f9b3f47390660909b68e1d3ecd840bd024128513c9a26.
def localCycle00216 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 18 2, .gapLower 1 3]

-- Cycle fingerprint be083eb0ce150b4ed8512d2d31b94db5859df07c0eda3e2c134997a865a1c899.
def localCycle00217 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 0 5, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -1, 0, 1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true, false] }
  origin := ![.triangle 29 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 0]

-- Cycle fingerprint be78bd4f89101dbd402a5721346509a8681803ac1179ad9d21b49886bae8f2c6.
def localCycle00218 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint beb8fb5aafad0eff6ca86c4cbdd457c573acb9b0b0388ea5b09f74fb37820392.
def localCycle00219 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 5, .distance 1 6]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint bf9e981f3be9c2cc70f74cb9a6e6fb3f31794b4ebd637fa1206cf2ef9002eecc.
def localCycle00220 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint c11bf8cd396cc82770cf3c9cebb0a60e00f8694018f1c9c11e141d631278a9f9.
def localCycle00221 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 6 0, .gapLower 4 0]

-- Cycle fingerprint c32660b1c814d36f119637d5f1fe648654e250f89ef458559bf780992771d217.
def localCycle00222 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint c44756e5b13bc3e7ab74c4d1866876fcbad20afcbd2fdfc42bdb7976c13f35bb.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c44c067dc3a0d7748d9ecdb335d6dc3fe63c5ad8cd0bad51c52a57083fbcbd7f.
def localCycle00224 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![0, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint c4edb52769a32006299f180b90f4abd6f72662c3573d0e756c67e2d4305637af.
def localCycle00225 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint c504cafd44e8760570f87e1c6d024c18aa4493a28a098d33db9e3887780fb9a9.
def localCycle00226 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint c56a57bc9d5377b5f8d400f18bfcdf370f83b18cd2b434c64b4f01953dca67e5.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 24 1, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint c59b2ae221131ca1c0fa787476e152d6e1b6b6c46409865dae1374feab273c13.
def localCycle00228 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint c68007083e2316951f4135023563ae92428a598f53fbf7d8998152b5f75d8462.
def localCycle00229 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 3]
    constant := ![-1, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 11 1]

-- Cycle fingerprint c6950fedc2a3b1020150c3355a05a79cb9048efc73b5792b2c9bc69719e0dd78.
def localCycle00230 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![0, -2, -2, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint c6ad236c4a030cd384e8cb3afea5b644c5e28b6a6553891fa6cb93afee8566c7.
def localCycle00231 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c8a42c5bc2bc92d056eff0d9ffbd3c5355f99fea881ddb7998ca6647d29f65c1.
def localCycle00232 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 18 2, .triangle 21 1]

-- Cycle fingerprint c8da06ac533ec7260c0ae5e4b4e3af3a1379b8b1dc9ccd7f9145480c4a61562a.
def localCycle00233 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 32 1, .gapLower 3 2, .triangle 1 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint ca0a44f4ab3b31ffe12d3766a69b6668b03038924852ac9215858892e346da95.
def localCycle00234 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 1 6, .distance 1 2, .distance 1 4]
    constant := ![0, 2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 19 1, .gapUpper 3 3, .triangle 21 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint cc1226dbecacb224c7e7981feb36698fbd101344600f9842532f7ac539da88fe.
def localCycle00235 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, 0, 0, -2, 0, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .triangle 18 2, .gapLower 1 5, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint cc58c43e7c2c77b07e36b1b8e8af15fc5f1c52b89b487dfdb60917633c840982.
def localCycle00236 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4]
    constant := ![0, -1, -1, 0, 0, 3, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 19 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint cceffbdf883264b37065a0c13516df3a4ee5b9991ae2b6f63f32bad16fbaafa6.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 2 3, .theta 2, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4]
    constant := ![-1, -1, 4, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.triangle 25 0, .corridorLower 2 3, .gapLower 2 6, .gapLower 5 3, .gapLower 1 5, .gapLower 1 4, .triangle 21 1, .triangle 19 0]

-- Cycle fingerprint cd2b89ab1947b4fb599ebd684fef1c759f5d46614a67db9512c3664d06b234da.
def localCycle00238 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 21 1, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint cdc558b4a13fdd35178ff50b92da4d0bd92c218bbf040f6fb4bfed972b54ed1c.
def localCycle00239 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint ce3cd7007b82feb72005cd283bef7928a37b45e24f66be598429a762356a98e3.
def localCycle00240 : Cycle where
  length := 6
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 2 5]
    constant := ![-1, -2, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 17 0, .gapLower 1 3, .triangle 19 1, .gapUpper 3 3, .gapLower 5 4, .gapLower 5 3]

-- Cycle fingerprint ce6583d214a7085fa4859c46071759e86331857f8ffede16c9cb4b1a109989e2.
def localCycle00241 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 2, .triangle 17 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ce98ff022cf8c3695763c9230576622106596a3ebe1bb36271ca640b2f675799.
def localCycle00242 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint d07b92d5e09768b2aa845a71a642c533b0c4d13cc74f6dd43b57a3a39c271b5a.
def localCycle00243 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, -2, -1, -1, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 4, .triangle 16 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0]

-- Cycle fingerprint d1bf28b72fd1da7c76e940232ddb2f0b550fe9ce046ba3f3ebdd5e9f7a661d9b.
def localCycle00244 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 2, .distance 2 4, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5]
    constant := ![0, -2, -2, 0, -1, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 6 0, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4]

-- Cycle fingerprint d43dbfc69b4e2ed85dce24e986e9255695c33874c9753fcbc520c920e728a73a.
def localCycle00245 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, 0, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .triangle 23 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint d567b38293ca8221cf6f0c01a0db814b805723e54860a3c3f8b61668900c7a3d.
def localCycle00246 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 17 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d5d30b1c6bd0c7ab77da5ba0f3d005b046788ecf07fd7509956693112649b3da.
def localCycle00247 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint d5f488fd0e9d0d74b94ac078d3feddf3a12ad53e35b78e1145b26cdad657f401.
def localCycle00248 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 3 4, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1, .triangle 19 0, .triangle 9 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint d70016b7b36eb219acc2acc9c3ee632a4b58f10f7340122ec827340827dda8c1.
def localCycle00249 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 24 0, .triangle 14 0, .gapLower 0 4]

-- Cycle fingerprint d803954211427ba8ff8160cfd7cbede4838496cdcbdc16fe1a3b44e4ca3bcb8d.
def localCycle00250 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, -1, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint d8237aeaf0780d8491bf7ece781ca9b8c6918ca23ff7b475f685920a2b59ec01.
def localCycle00251 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint d967b4869fecf9f6845802ad4100552f22e5638beab30f14a95435dbf29eb6fa.
def localCycle00252 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint da7fc2fa6130c3e198c77e367614a48f28c15f7838e00ee5f249883cddd087ba.
def localCycle00253 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -2, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint db062c68dac853547e4b6ad7fb2c73ac7edde55219cea0817e9adbda7fcb6dd3.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 3]
    constant := ![-1, -1, -1, 0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true] }
  origin := ![.triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 15 2]

-- Cycle fingerprint db557d2021a0015a51eb79918dd0707ada3688901c26e29b34d42f5b4d8bdeff.
def localCycle00255 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6]
    constant := ![-2, 0, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 2, .gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 2]

-- Cycle fingerprint dc5b9b739223e58a342c7d7bf5acb4954f2aa6dcc1b40df9251af52e9c1a7e58.
def localCycle00256 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint e01ab1cd83be85df42c57ae816f1996fdb9d16853d9ba2d6af39caf297cde2bc.
def localCycle00257 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint e1375111f4d8c16570bac7455c0012f1c9fc5b34cac59a492867d1e8bf4ae913.
def localCycle00258 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 16 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint e27047842767959bdfad06219fc6ffec921e93c2b1ecef9134f455cb5908e9aa.
def localCycle00259 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 32 1, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint e31cd20ac8a54d1eefce3219478e06ab846a5ba96bb6fcda5299633ee15eca88.
def localCycle00260 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint e37296b2a682f9f59530ca202e0bd159617c651b075070857bb8aca8e865b3bd.
def localCycle00261 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .corridorLower 3 6]

-- Cycle fingerprint e49a54472257d77adf6af5ceb972ef6917ea6534124d55c81e161d6e66e8e215.
def localCycle00262 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 1 5, .distance 1 2, .distance 1 3, .distance 1 6, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, 0, -2, 0, 0, -2, 0, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 15 2, .triangle 21 2, .gapLower 1 2, .triangle 19 1, .triangle 25 0, .corridorLower 2 3, .thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint e4d58c68da050fc36ae4a1c7d4d25e820831be122a29754e267d4d20e98eb52d.
def localCycle00263 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint e51e9efe628672648f5fb2a73d62d9d41393731ac29fa03362b57aeae456bcb1.
def localCycle00264 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint e64453e893135dcf0dd091d83122c86a99392b2180b1e2591f814215e3f9cbcf.
def localCycle00265 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 5, .distance 1 5, .distance 1 2, .distance 1 4]
    constant := ![0, 2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 19 1, .gapUpper 3 3, .triangle 20 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint e64a517283c8441da6d577c1b24a2c98910a33ba058a808d2b6a20ae2cda5a52.
def localCycle00266 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 21 0, .triangle 19 0, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint e678b95afded36f5e849ab16311035e8ca5ce14acd056dc3b4086b66b6dfbed8.
def localCycle00267 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint ea18f63e92504dfbe0e76877dfdbd397c1ea9ad9153be35b9772f12a3edd0b8d.
def localCycle00268 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 0 0]

-- Cycle fingerprint ea42a9d337d3476364e406cab6a3d49d5cf4e617eacedf0d2538827cda8d5096.
def localCycle00269 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ebb4b743d7169a78ae437419e79a42da3e2c84e984dd7d38511f6f2dd6c04f9b.
def localCycle00270 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint ebc01b42dc58a8c6a7ddc9189fbb9217fee02a6317808255fe549f92420e2178.
def localCycle00271 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint ebff5b1e620ed2b6d28cdc4d742474bebd57824bbb708c2f6b10b3bfb87cae60.
def localCycle00272 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 2]
    constant := ![-1, 0, -1, 0, 2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 4 2, .triangle 8 1]

-- Cycle fingerprint ed33b964f9147ed4b2cd4e75546cda30ab16b2c0cf14779fa1ae591a0264fbda.
def localCycle00273 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ed67212dbbcc6bc9aa13eeb80bc82179cdd18730faa5d30dbf77700fccb110a1.
def localCycle00274 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapLower 1 5, .triangle 17 1, .triangle 0 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint ee5b207aa6ce4f20d7a87890a4109f0925a23edb3e329e068ffdee1aaa83c82e.
def localCycle00275 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![2, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 6, .triangle 17 1, .gapLower 1 3, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint f04f61890bf2990d89e72b5117b836de9a9ecc7065fa2f69e2314e5902195936.
def localCycle00276 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint f193d31e86beb6abd837ba45b4530a970693782b4a0a6154b91c33b94115c0e6.
def localCycle00277 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 29 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 0 2, .triangle 8 0]

-- Cycle fingerprint f254724245ec743c9632f872bc524e090e32f2b0e903900d97027299c023feb3.
def localCycle00278 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f3939edb02fdf3de4035c9115908d19944ca90678494d7a7e164ab172ce85e60.
def localCycle00279 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 26 0, .corridorLower 3 5]

-- Cycle fingerprint f44a9fe16ef347dcedb254a5b55a18b63b6a17e13464dd31e0bfeeae99be500f.
def localCycle00280 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3]
    constant := ![2, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false] }
  origin := ![.gapUpper 3 3, .triangle 26 2, .triangle 17 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint f50bc10a7fe62e66920b9a6489fea70c077ad9d5301245ba15dc161541bc7547.
def localCycle00281 : Cycle where
  length := 6
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 2 6]
    constant := ![-1, -2, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.triangle 18 0, .gapLower 1 3, .triangle 19 1, .gapUpper 3 3, .gapLower 6 5, .gapLower 6 4]

-- Cycle fingerprint f5d551a313171b248b2c8eaf9ca11e41ad7054514d6ef0c5e562296209a3b8d5.
def localCycle00282 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, -1, 0, 1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 24 0, .triangle 14 0, .gapLower 0 4]

-- Cycle fingerprint f662d93aff522a5ceb111dec2fea04deab3ba1140adc9d2da4f7b3c0b99c902a.
def localCycle00283 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 6 0, .triangle 5 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint f7237f9ab3bd4a4f0b9a95304a848c5dcdf450c1851033991379b03dd4890f9f.
def localCycle00284 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5]
    constant := ![0, -3, -1, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4]

-- Cycle fingerprint f7595c654a726c8425ff13510f873fef44cfb983ab0a7156e40ab50803438a9c.
def localCycle00285 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .distance 2 5, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, -1, -1, 4, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .gapLower 2 6, .triangle 17 0, .triangle 18 2]

-- Cycle fingerprint f87b7eb6f71e5d4c667ed5875802b7945b61be3b70635f121d1bde8e01c44edf.
def localCycle00286 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 4 5, .distance 4 6, .distance 2 6, .distance 1 6, .distance 1 2, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![-1, 0, 0, 0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 0, .triangle 34 2, .gapLower 6 4, .triangle 18 2, .gapLower 1 4, .triangle 16 2, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint f8d6b11f6972fcdd79af245dd2b6b4e871887fe0cbd75869009fd24a3389ba21.
def localCycle00287 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .corridorLower 5 6]

-- Cycle fingerprint fbca1d67ef23dc6e4bdb06b85cca9da56808758a8abecf833f1756c9cc29fe64.
def localCycle00288 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint fc3b4792351d4460ae0cc339acf212451a5e162b07cabafda0dc39af7939d8b5.
def localCycle00289 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fd89e8a67205ac0fda036012beea0c5cb14eca8f41d86837fb3e77bfaf73497d.
def localCycle00290 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2]

-- Cycle fingerprint fdfcc916920d04ec3d8c11bf21c7d9d039a023923d6e10606491b2df3a7826c6.
def localCycle00291 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![0, 0, 3, 0, 0, -1, -3, 0, -1, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 2, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .gapLower 1 4, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Cycle fingerprint ff648901d05733cc48212472440ec211021cac99d3d328833a220cdc9022386f.
def localCycle00292 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .distance 1 5, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![0, -1, -1, 0, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, false] }
  origin := ![.triangle 19 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .triangle 17 1, .triangle 18 2, .gapLower 1 2]

def library : Library := fun id => if id < 146 then (if id < 73 then (if id < 36 then (if id < 18 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 13 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))) else (if id < 15 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))))) else (if id < 27 then (if id < 22 then (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))))) else (if id < 31 then (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))) else (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))))))) else (if id < 54 then (if id < 45 then (if id < 40 then (if id < 38 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none)) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 42 then (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))) else (if id < 49 then (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none))) else (if id < 51 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)))))) else (if id < 63 then (if id < 58 then (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))))) else (if id < 68 then (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))))))) else (if id < 109 then (if id < 91 then (if id < 82 then (if id < 77 then (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none))) else (if id < 79 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))))) else (if id < 86 then (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)))))) else (if id < 100 then (if id < 95 then (if id < 93 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))) else (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))))) else (if id < 104 then (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))) else (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))))))) else (if id < 127 then (if id < 118 then (if id < 113 then (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))))) else (if id < 122 then (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))))) else (if id < 136 then (if id < 131 then (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))))) else (if id < 141 then (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)))) else (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))))))))) else (if id < 219 then (if id < 182 then (if id < 164 then (if id < 155 then (if id < 150 then (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))) else (if id < 152 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))))) else (if id < 159 then (if id < 157 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))) else (if id < 161 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)))))) else (if id < 173 then (if id < 168 then (if id < 166 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))) else (if id < 170 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))))) else (if id < 177 then (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none))))))) else (if id < 200 then (if id < 191 then (if id < 186 then (if id < 184 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none)) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))) else (if id < 188 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))))) else (if id < 195 then (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none))) else (if id < 197 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)))))) else (if id < 209 then (if id < 204 then (if id < 202 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)) else (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none))) else (if id < 206 then (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none))))) else (if id < 214 then (if id < 211 then (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id = 210 then some localCycle00210 else none)) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)))) else (if id < 216 then (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none)) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)))))))) else (if id < 256 then (if id < 237 then (if id < 228 then (if id < 223 then (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none))) else (if id < 225 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none))))) else (if id < 232 then (if id < 230 then (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none))) else (if id < 234 then (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none)) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none)))))) else (if id < 246 then (if id < 241 then (if id < 239 then (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none))) else (if id < 243 then (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none)) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none))))) else (if id < 251 then (if id < 248 then (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none)) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none)))) else (if id < 253 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none))))))) else (if id < 274 then (if id < 265 then (if id < 260 then (if id < 258 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none))) else (if id < 262 then (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none)) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none))))) else (if id < 269 then (if id < 267 then (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none)) else (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none))) else (if id < 271 then (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none)) else (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none)))))) else (if id < 283 then (if id < 278 then (if id < 276 then (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id = 275 then some localCycle00275 else none)) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none))) else (if id < 280 then (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none)) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none))))) else (if id < 288 then (if id < 285 then (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id = 284 then some localCycle00284 else none)) else (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id = 287 then some localCycle00287 else none)))) else (if id < 290 then (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id = 289 then some localCycle00289 else none)) else (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id = 292 then some localCycle00292 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 4, 3, 6, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 2, 3, 0, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 107 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5248)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 4, 6, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 4, 6, 1], ![5, 0, 2, 3, 1, 6], ![4, 2, 3, 0, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 259 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5249)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 6, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 2, 3, 0, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 183 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5250)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 6, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 2, 3, 0, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 190 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5251)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 6, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 2, 3, 0, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 222 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5252)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 2, 3, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 112 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5253)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 4, 6, 1], ![2, 5, 0, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 2, 3, 0, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 190 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5254)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 2, 3, 0, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 222 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5255)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 6, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 3, 0, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 167 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5256)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 0, 6, 4, 1], ![2, 5, 0, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 3, 0, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 251 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5257)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 5, 6, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 0, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 3, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 247 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5258)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 0, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 3, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 251 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5259)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 5, 6, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 6, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 3, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 80 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5260)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 6, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 3, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 80 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5261)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 5, 6, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 3, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 152 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5262)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 5, 6, 0, 4, 1], ![2, 6, 5, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 2, 6, 3, 0, 1], ![4, 2, 5, 3, 0, 1]], proof := .tail 17 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5263)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 5, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 116 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5264)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![3, 6, 5, 0, 4, 1], ![2, 6, 5, 0, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 154 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5265)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 5, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 2, 3, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 12 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5266)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![6, 3, 5, 0, 4, 1], ![6, 2, 5, 0, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 2, 3, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 261 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5267)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 4, 3, 2, 6], ![5, 3, 0, 4, 1, 6], ![5, 2, 0, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 266 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5268)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 4, 3, 6, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 0, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 266 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5269)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 4, 6, 3, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 0, 4, 6, 1], ![5, 0, 2, 3, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 283 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5270)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 6, 4, 3, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 0, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 3, 2, 0, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 231 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5271)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 6, 4, 3, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 0, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 3, 2, 0, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 179 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5272)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 5, 6, 4, 3, 2], ![5, 3, 0, 6, 4, 1], ![5, 2, 0, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 3, 2, 0, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 279 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5273)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 0, 4, 6, 1], ![5, 0, 2, 3, 6, 1], ![4, 3, 2, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 76 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5274)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![5, 3, 0, 4, 6, 1], ![5, 2, 0, 6, 4, 1], ![5, 0, 2, 6, 3, 1], ![4, 3, 2, 0, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 179 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5275)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 5, 3, 2, 4, 6], ![0, 6, 5, 4, 3, 2], ![5, 3, 0, 6, 4, 1], ![5, 2, 0, 6, 4, 1], ![5, 0, 6, 2, 3, 1], ![4, 3, 2, 0, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 279 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5276)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 5, 6, 4, 3, 2], ![5, 3, 0, 6, 4, 1], ![5, 2, 0, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 2, 0, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 49 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5277)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 5, 3, 2, 6, 4], ![0, 6, 5, 4, 3, 2], ![5, 3, 0, 6, 4, 1], ![5, 2, 0, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 2, 0, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 264 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5278)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 5, 6, 4, 3, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 0, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 2, 0, 1, 6], ![4, 2, 0, 3, 1, 5]], proof := .tail 145 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5279)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 5, 3, 6, 2, 4], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 0, 6, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 2, 0, 6, 1], ![4, 2, 0, 3, 5, 1]], proof := .tail 145 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5280)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 5, 6, 4, 3, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 6, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 2, 0, 1, 6], ![4, 2, 3, 0, 1, 5]], proof := .tail 198 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5281)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 6, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 2, 0, 6, 1], ![4, 2, 3, 0, 5, 1]], proof := .tail 198 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5282)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![5, 3, 6, 0, 4, 1], ![5, 2, 6, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 2, 6, 0, 1], ![4, 2, 3, 5, 0, 1]], proof := .tail 46 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5283)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 5, 6, 4, 3, 2], ![5, 6, 3, 0, 4, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 47 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5284)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 5, 6, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![5, 6, 3, 0, 4, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 47 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5285)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![5, 6, 3, 0, 4, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 78 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5286)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 0, 4, 1], ![5, 6, 2, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 9 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5287)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 0, 4, 1], ![6, 5, 2, 0, 4, 1], ![5, 6, 0, 2, 3, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 150 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5288)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 6, 5, 3, 2, 4], ![0, 6, 5, 4, 3, 2], ![6, 5, 3, 0, 4, 1], ![6, 5, 2, 0, 4, 1], ![6, 5, 0, 2, 3, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 160 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5289)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 178 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5290)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 1, 4, 5, 6], ![2, 0, 1, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 20 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5291)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 226 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5292)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .low (![126, 75, 131, 121, 40, 77, 103, 187, 260, 72, 127, 274, 205, 118, 239, 171, 161, 157, 28, 82, 114, 243, 269, 182, 175, 137, 203, 8]) }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5293)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low (![158, 75, 131, 104, 165, 124, 282, 4, 260, 96, 268, 242, 71, 252, 239, 180, 155, 249, 267, 258, 188, 249, 253, 67, 249, 60, 153, 191]) }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5294)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 10 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5295)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 41 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5296)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 41 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5297)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 38 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5298)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 38 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5299)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 1, 3]], proof := .tail 208 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5300)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 3, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 73 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5301)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![158, 75, 131, 104, 165, 218, 55, 4, 260, 96, 268, 197, 71, 252, 239, 180, 155, 157, 267, 258, 188, 228, 253, 67, 117, 60, 153, 219]) }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5302)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 1 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5303)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 270 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5304)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 4, 3]], proof := .tail 270 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5305)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 1, 3]], proof := .tail 212 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5306)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 3, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 271 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5307)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 1, 4, 6, 5], ![2, 0, 1, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low (![194, 75, 131, 141, 93, 135, 217, 4, 19, 95, 125, 210, 71, 148, 58, 146, 200, 157, 278, 185, 256, 120, 225, 7, 25, 109, 81, 277]) }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5308)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 4, 3]], proof := .tail 144 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5309)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 1, 6, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 4, 1, 3]], proof := .tail 143 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5310)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 1, 6, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 0, 1, 3]], proof := .tail 143 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5311)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 0, 1, 6, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 0, 1, 3]], proof := .tail 53 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5312)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 3, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 4, 3, 1]], proof := .tail 100 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5313)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 3, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 6, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 0, 3, 1]], proof := .tail 18 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5314)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 3, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 0, 6, 1, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 0, 3, 1]], proof := .tail 140 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5315)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 6, 0, 1, 4, 5], ![2, 6, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 163 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5316)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 6, 0, 1, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 181 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5317)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 2, 5], ![6, 3, 4, 0, 1, 5], ![6, 2, 0, 1, 4, 5], ![6, 2, 0, 1, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 11 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5318)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 241 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5319)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .low (![174, 224, 83, 79, 29, 189, 103, 230, 206, 24, 149, 193, 205, 177, 246, 172, 235, 273, 280, 173, 204, 204, 265, 240, 240, 105, 227, 8]) }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5320)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 34 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5321)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 147 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5322)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 61 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5323)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 2, 4, 3]], proof := .tail 115 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5324)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 1, 4, 3]], proof := .tail 221 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5325)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 3, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 4, 1, 3]], proof := .tail 27 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5326)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 3, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 2, 4, 3, 1]], proof := .tail 27 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5327)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 4, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .low (![209, 98, 214, 134, 16, 284, 55, 176, 290, 213, 89, 56, 71, 68, 91, 286, 130, 289, 250, 170, 168, 168, 234, 281, 281, 244, 153, 272]) }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5328)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 4, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 1, 4, 3]], proof := .tail 221 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5329)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 3, 6, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 4, 1, 3]], proof := .tail 27 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5330)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 3, 4, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 2, 4, 3, 1]], proof := .tail 27 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5331)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 4, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 0, 1, 4, 3]], proof := .tail 62 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5332)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 3, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 1, 6, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 0, 4, 1, 3]], proof := .tail 33 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5333)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 1, 6, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 0, 1, 3]], proof := .tail 26 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5334)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 3, 6, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 0, 1, 6, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 84 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5335)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 3, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 0, 4, 3, 1]], proof := .tail 33 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5336)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 3, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 6, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 0, 3, 1]], proof := .tail 26 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5337)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 3, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 0, 6, 1, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 84 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5338)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 4, 3, 0, 1]], proof := .tail 26 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5339)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 6, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 84 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5340)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 3, 4, 2, 5], ![6, 3, 4, 0, 1, 5], ![6, 2, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 129 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5341)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 139 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5342)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 4, 1, 5, 6], ![2, 0, 3, 1, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 159 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5343)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 36 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5344)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 14 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5345)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low (![201, 102, 132, 30, 63, 124, 35, 64, 142, 184, 65, 248, 71, 276, 22, 65, 220, 249, 6, 196, 276, 276, 113, 151, 275, 66, 254, 69]) }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5346)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 3, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 38 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5347)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 4, 6, 3, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 52 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5348)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 3, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 186 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5349)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 3, 4, 2, 5, 6], ![0, 6, 4, 3, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 164 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5350)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 4, 3, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![201, 102, 132, 30, 63, 3, 35, 64, 142, 184, 65, 5, 71, 276, 22, 65, 220, 101, 6, 196, 276, 276, 113, 151, 275, 66, 254, 69]) }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5351)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 4, 3, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 270 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5352)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 4, 6, 3, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 32 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5353)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 4, 1]], proof := .tail 186 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5354)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 4, 2, 6, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 4, 3, 1]], proof := .tail 119 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5355)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 4, 3, 6, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 4, 1, 6, 5], ![2, 0, 3, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .low (![106, 43, 132, 99, 291, 135, 42, 245, 238, 156, 136, 202, 71, 276, 207, 257, 87, 97, 285, 13, 276, 276, 44, 211, 216, 237, 45, 232]) }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5356)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 4, 6, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .low (![233, 43, 122, 85, 0, 74, 162, 245, 94, 223, 128, 48, 71, 90, 21, 128, 48, 54, 236, 128, 262, 292, 128, 110, 39, 92, 59, 199]) }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5357)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 4, 6, 1, 5], ![2, 0, 3, 6, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 3, 4, 1]], proof := .tail 186 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5358)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 4, 6, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 6, 4, 1, 5], ![2, 0, 6, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 4, 3, 1]], proof := .tail 263 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5359)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 0, 6, 4, 1, 5], ![2, 6, 0, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 0, 3, 1]], proof := .tail 57 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5360)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 6, 4, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 0, 6, 4, 1, 5], ![6, 2, 0, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 0, 3, 1]], proof := .tail 50 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5361)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 4, 6, 0, 1, 5], ![2, 6, 0, 4, 1, 5], ![2, 6, 0, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 3, 0, 1]], proof := .tail 287 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5362)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 4, 3, 2, 5], ![3, 6, 4, 0, 1, 5], ![2, 6, 0, 4, 1, 5], ![6, 2, 0, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 195 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5363)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 6, 3, 4, 2, 5], ![0, 6, 4, 3, 2, 5], ![6, 3, 4, 0, 1, 5], ![6, 2, 0, 4, 1, 5], ![6, 2, 0, 3, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 169 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5364)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 215 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5365)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 4, 0, 1, 5, 6], ![2, 3, 0, 1, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 108 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5366)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![3, 4, 0, 1, 5, 6], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 166 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5367)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 2, 5, 6], ![3, 4, 0, 1, 6, 5], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 31 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5368)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 88 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5369)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 3, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 138 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5370)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 4, 6, 3, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 37 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5371)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 4, 3, 2, 5, 6], ![0, 6, 4, 3, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 6, 1, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 15 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5372)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 3, 2, 6, 5], ![3, 4, 0, 1, 6, 5], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![23, 102, 123, 30, 63, 111, 86, 64, 142, 184, 268, 197, 71, 276, 22, 65, 220, 2, 6, 255, 276, 276, 113, 51, 133, 70, 192, 229]) }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5373)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 3, 6, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 4, 0, 1, 6, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 288 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5374)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 4, 3, 2, 6, 5], ![0, 4, 6, 3, 2, 5], ![3, 4, 0, 6, 1, 5], ![2, 4, 0, 6, 1, 5], ![2, 3, 0, 1, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 37 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 5375)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (5248 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 5248 ≤ id.val) (hhigh : id.val < 5376) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 5248)) = true := by
  let j : Fin 128 := ⟨id.val - 5248, by omega⟩
  have hsum : 5248 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (5248 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard041
