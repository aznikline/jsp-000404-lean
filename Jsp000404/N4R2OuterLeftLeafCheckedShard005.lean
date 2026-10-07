import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard005
open N4R2OuterLeftReplay

-- Cycle fingerprint 0002556566bf24d2ff66039eccb53ce241a8133a59fed3baad27b2a13902cb52.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 16 1, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 00521f72536de6fae549ba98f60c026256a1dc5370d49df5dae1f46852ffbffd.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 0088bea689d5ad9e56fcba5aaaec0caaa842b5fc531b3bf41f7c2d713d1017fa.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 23 2, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0]

-- Cycle fingerprint 00f85653fed483a1b1a6a17d7ee49ab964d22c47de5582da1a9f28cb1b521241.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 014c56d3b555edbde55b66bc4984269eb19a79607b775c8f834e4e84a306d9ff.
def localCycle00004 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 0223a589ad70eeb04e9378e98b1dc8e546101d29d639a55d107a9eee2e053feb.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 034203772c447a0753e7ec3a25be553dc1fb26ab60632806d729095e196ea304.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 03a80279cafd536a6fcf050634fbe0e8dac07f27ac87e612014f2ba526917697.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2]

-- Cycle fingerprint 03db72f9466d7960fa48ed64a37fdf8b9cc051da231374663e50727f97572d7e.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 2, .distance 1 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 17 1, .triangle 30 0, .triangle 14 0, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 04e48b1159ee5accedab0d1f1d0ff521dd679b002263405f76eee831cfd0655f.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 056be970e3c23bad3bdcfbccba693d8f68a8dc55ef8329788ec747900d7597cb.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 21 2, .gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 056d22a9891d7eb5a14624560d3d7551d37ba67b73bc048901769a754e6778bf.
def localCycle00011 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 2]

-- Cycle fingerprint 06bfc8704aab047976c73a781c9a1c63f42bdf3f26ab509f4415a201f67c1c1d.
def localCycle00012 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 21 2, .gapLower 1 2, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 080374ffeefb80f3401e3cd6e14487afb5c39250925176e8eda218bbb626a463.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0]

-- Cycle fingerprint 084ecb729763235ee8b12561f0dbb171cede355f75dfa5661607578dd8c79188.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 08b4a54d2a160328e30bb09c2177dd1c228f4cce1fb5b1d338acb9ef80fa603c.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 20 2, .gapLower 1 1]

-- Cycle fingerprint 08f2d2e1c72defeeae8c21202c30cf5deebc60c781fd1ec8cb57c45c843d9bb6.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 08f61f794e29390d6d52ae26198e12dc430c0204e93201b931a2807b6c0f252d.
def localCycle00017 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 29 2, .gapUpper 2 5]

-- Cycle fingerprint 097491495a622e5f7be30b8f368ac60baf009f4e5df82e16f745538c4561ebfd.
def localCycle00018 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 18 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint 0b25a211d3b5bf28f45b98309352341efdb0f12e4e07e1696cd0c74edea5bccd.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -1, 0, -1, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 29 0, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 0c435c27adfc1f12555a10a6185d8b90d0e51b0c06e4803fcd8411ecfe2812dc.
def localCycle00020 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 16 2, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 0c48d46f7631445603b3adafe5d9dc4be1b554d36ab13fd77becdc1bd25d242b.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4]
    constant := ![3, -1, 0, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4]

-- Cycle fingerprint 0d3df9f8f43f6d381c9c448a3335d10ace72209edeb21eeb51e9b4d1842a7b80.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 0e48e8b36b4a52db7bedd9da68b976a0712eabcf9f11194fc7603eb673b98054.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 0e889a7165c23cdfc8fd6e16ae29adb27d8b6704327907be8aa8895c2e3ec6e4.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 21 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 0eaa91d9f3f9ad751d5716eae9c8f76e212a66132f1cd624b4dd0628c98f04ed.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 2 6, .distance 3 6, .distance 4 6]
    constant := ![0, -1, 3, -1, -3, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 18 1, .triangle 27 1, .triangle 32 1]

-- Cycle fingerprint 0eb5f16c3294ede1b5210b24d702cd9ca9e6829c4199001d46b9376ad160e346.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 0f87001adf4326208981a4fe043729283fab5678a4909bb15378f78eb762efa9.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 10cd44cd69dce836c954ddcd43d2e6cd44519bf66564b5b68f6c8037cf5db02a.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 11aa46739f9fe82a167c5ce1111ce56542c99f8539cd559f1d3d5dd4a3ff1ba7.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 22 1, .triangle 28 0]

-- Cycle fingerprint 128ccc755a50ffcf60527ce8f02077844954a3fe25fe77128e83e96f10fe0094.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 20 1, .gapLower 1 3, .triangle 4 0]

-- Cycle fingerprint 13617db116de09efdfcbe4e6572bb50a9ffb21b5a108586c4aba5c898f92a233.
def localCycle00031 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0]

-- Cycle fingerprint 14465e01e2a3408c8c7ea05953591cf33bac2f0b9bd88bb96bb4cae8a299ddba.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 16 1, .triangle 25 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 159678bdfdb91b51ad056146ef0da2f6b693ccc2f024aec83dce3020ac2790fd.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 1669545606e7047266e84bb34f3e3622b90d94c84a85f79c07372b91781c05b6.
def localCycle00034 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 16ebaafb82ca4f0133e9d619b2b42383d3a33802e8a0195a2045705f2a9eef50.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![-1, -3, 0, 0, 3, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2]

-- Cycle fingerprint 188d97385e8470f330136a7cdb6a540a33b2188c24f29c30d98e9be285d7f1f0.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 192d14574888266da5915f58a7c5831ba5fc453909b755c0e7f30d5efd767d2e.
def localCycle00037 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1a3d40cd33741716f86b50e16aff83a700d91aeca5c6410547c7f3c024832450.
def localCycle00038 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 16 1, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 1a77424dec084a88d1036ac1fc7d6b1123d4c8c673aef3efade66fc0b3c4a5ef.
def localCycle00039 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 1da8b2152a84945af0201828a60fa6b8ce6a01ddd94292a2b5fb9b3337370449.
def localCycle00040 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint 1e9574596dd6e02c3b7d94dbaca780e402acbdaa61b0576e3039be37a5f8120a.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3]

-- Cycle fingerprint 1fbe7eecb892757dc8632ac757ba52f41b2fc48862fd1633252ecc33fb54d57b.
def localCycle00042 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2]

-- Cycle fingerprint 21c8f6f86e326258fb211c36a59597dea0f34028cc2dbc805e06eabc893aced9.
def localCycle00043 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 21fa40e9e8a5296b8aa30bb4198bd71caab53d343f9e8e02e5a665e11adf618f.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 5]
    constant := ![0, -1, 0, -1, 0, -1, 0, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 26 1, .triangle 27 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 17 0]

-- Cycle fingerprint 2209ae8e5b7883684b7ec12aa2b1599a2f06b921b40107f6f37bba641c67a7a2.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-1, 0, -1, -1, 0, 0, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 17 0, .triangle 26 1, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 221766d605aa7fdf5995b9bf97ade094d6bcbd7a14b690c8f1a22ee1eabd1c80.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![3, -2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 24 2, .gapLower 1 3, .triangle 15 1, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 226c799c4be604eeb184814466e9d16d4f399b9fd71325779fb9888ca5c8435a.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![-1, -2, -2, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0]

-- Cycle fingerprint 2310831546264af27b0fa2e3bf73a4aeac998201d692dfee5ecfeeb9925b589e.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-1, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 238ddb4e2f955e560487037a2f4fa8f8654d717595cd5b6ac1c0590bf08e32f8.
def localCycle00049 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 30 2, .gapUpper 2 5]

-- Cycle fingerprint 23a3252b33bb997809eca313ca9af0fa496be914d49615603d587986c15103e4.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, 0, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint 23f13e2e43c690e55a34c522967d5195ade8476b70cc26124b507cf6537d011d.
def localCycle00051 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -2, 0, 0, -1, 0, 0, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 16 1, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 24ba3179a9053286c661b3b2af700606300372f9dedd7d8de48e8b70d1ac4eea.
def localCycle00052 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 25d297b41684e114a4ad5bc24d8cca501bb328dcd3b291b71017ea180519e679.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint 2651259092793db88212e81b4e1ffe309341794f339eddb31627acfda3781feb.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 21 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 265b6d559ece5ee5ca144f0be6e912803d8c97f0d6ca0cbe5215a304e8b2ae55.
def localCycle00055 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 15 1, .triangle 5 0]

-- Cycle fingerprint 26d004cbd8c590c6525b9c3d931ea397b826bcd8fed29cdf5918fef4fc57e462.
def localCycle00056 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 2712ecca356b374489cd81f7260bb5270d82add2700d91d9e1fc54f8f90a21b5.
def localCycle00057 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 2, .triangle 26 1]

-- Cycle fingerprint 27b82362f5cd5dbd5c8e4c0a7c0edf3d082c02c0ba7bf2cfb5180c3e82ba35ba.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 22 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint 27cd48c5765bcf35ad995f4b0800779803cd66ec0c9f2982fc5662bfe1cdc3e8.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 20 1, .triangle 21 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 2824b3f498f39ff46b0604e2d537435841bf07f7b439c124789e912d4a66dc6b.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 4 5, .distance 2 4, .distance 2 3]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 22 1, .triangle 28 0, .gapLower 2 2]

-- Cycle fingerprint 283283512cc263c9f6e04a2d585ae5d7fdf403ef157fd50c707f958114ad52fb.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .triangle 12 0, .triangle 6 1, .gapLower 2 0]

-- Cycle fingerprint 29f841f70c8f70d6b4b31cac8c602a3882bfe296aa2a4281e68132107c9ced61.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 2, -2, -1, 0, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 2, .triangle 5 0, .gapLower 0 1]

-- Cycle fingerprint 2a7aeb9b11eebe60ce872de95c9a4c742e8ae85753c6dabbe513d45a92262885.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 2aa30f93523b5c5c4ab49f725fd1abc2c274eede440d9753e2c5a96557fc3e20.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 2af71584599cd2c1e4b83ae593a98fde5023d76521d423b9691ffa541464f7f1.
def localCycle00065 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 2be49b43af0eb66477303b2a63ee0aafbd6683730bce846239629eeee359ca68.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 2c3d8733aedca32718bacb50a682eefc52f528ca78532e84ad7c97b5233332cb.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2ce50af4befc9d8cb49521d350f31ebda2f6a548305fa326af1f5ec05bd9e84d.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6]
    constant := ![0, -1, 0, 0, 0, 3, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 34 1, .triangle 12 0, .gapLower 0 3, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 15 1, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint 2d3fa5b943b6e170d318be568d1c91627709a2fd81688836b012d013e4e0fe25.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 2, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 2e0e8c8d38814d1a0d11fd33863a0b53a9edbc0a76868f3e02fd56fcfb87587a.
def localCycle00070 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 5 3]

-- Cycle fingerprint 2e2c9d3d002b1ae4b99ff809c4ad33ffd3ceb58788e36cfa27d3bbcc489808dc.
def localCycle00071 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 1 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 20 0, .triangle 15 1, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 2e5e0b1f472fe3e928c3d454d15014161b66d185197d753522f04da1cf7013e4.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 2eeb717854d5534f136cafd416abc919a61db05b565fc8290a620ce26497f572.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 2f495bda69d0bd05508e19c42710d6a6880beb37a3acf1d9e457ba023108a014.
def localCycle00074 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-1, -1, 0, -1, 0, 0, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 16 0, .triangle 29 0, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 30430555e523eab82a5327a27a997c1dc6eb9dcb7b0f7284f68a0f795041be47.
def localCycle00075 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, 0, -3, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 31 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 26 0]

-- Cycle fingerprint 30c8f3226642d7ea84a7a0cb188266b82f3ef0e0435ad77412df90f07eac6389.
def localCycle00076 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, 0, 0, 3, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 15 1, .triangle 26 0]

-- Cycle fingerprint 3112f25e40cd201bcd2eabb70118fd679fb56ed7c020be54148243bb2d50b232.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3]
    constant := ![-1, 3, 0, 0, -3, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .gapLower 1 3, .triangle 23 1, .triangle 29 0, .gapLower 2 2]

-- Cycle fingerprint 314d335f91cf606b28803fbb47b9f0be5694d7a0bd67a6ea134d4d4fd267f55d.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 3196e7229cdf4289299a0e1bf306e6d7d6ae65f8c9cfbf29e93c1af7a7f0b685.
def localCycle00079 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -1, 0, 0, -3, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint 31c117cbab5ff50a277e7c2819d307d5cbe337e377fd656a208871b169ac3ebd.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 0, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 3, .triangle 6 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .triangle 30 0]

-- Cycle fingerprint 31c2206412be8aafa78cbeead9f69e0a25752ac8f89e8fe08edf9d5aa5eaecd2.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 323ade28f8caf9f55625036b6468a09d417d880a396facf5892ff0741d400341.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3263f66f60639555d7f7ccbee43f3c822eb57899d7d919c1ace12dfaa927d81d.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 32c206d900fab6e67b98539e2ef349f1704e0005a7cf038bf1ab64dbc65b242e.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 2 4]
    constant := ![-1, -1, 0, -1, 0, 0, 3, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 28 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 16 1]

-- Cycle fingerprint 340562d7a4ff97204092f3e43448b8760f4c7d560c2be2ace9606df5ec90fc0c.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6]
    constant := ![-1, -3, -1, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint 3420f627a5e67af9a45acc48db20c4733c2d13d05c9c7df455e890ffa0a0497b.
def localCycle00086 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 4, .distance 1 2, .distance 1 4, .distance 2 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 5, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 35181efb24849c9162378ef5768f4f909b1332295a6b10f180ed64119bd554cd.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 20 1, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 355736f1e1b7c834d99841ac76833a01beba6f0160e086d4d156a8d927de3b9a.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 1, .gapLower 1 6, .triangle 17 0, .triangle 26 1, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 357eb6b0d6e9cce2cffc9f50600c3aca24692be7f113dea576f88fce9d659a57.
def localCycle00089 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 1 5]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 24 0]

-- Cycle fingerprint 35b3fd3b16442ef5763971a8a31737052118e857f8ec7f2b06b7132a77b5f148.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 36639f445fded3b09424fb9d1ca79709057ab5019a0270f66959ed815908b905.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 21 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 372470ef793bc116f78e71869ddebd52d05acb58e8fb2429e65e601efd28e594.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 374cf1c3806f43f7ebd92e811e9e0274344af734e1cccd75b1d39feb067cc6bb.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 0, 0, 3, 0, 0, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 38c5bf27887b6677cf4539893d6dcc03c5d1d3e4dc03b84ab90a4e5075247f70.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 28 0, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint 3938f3a2c5f8683222e8f72064032b05ebea7511bba6545a11e6166d49bcaaaa.
def localCycle00095 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 5]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 39dcc7ebec18d24fb718be91bcfc3548f8f866fe8996ca6f7cfa5b5d31518c4e.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 3a18b8b65be2b0655f33d6d6fab02c4ac489fc1b7cdbb836456b66c5cd97424c.
def localCycle00097 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 3c1a9bae1abced6725cf0f2c2fcb11a4ac1b1debe63231a0da58603ead699ec2.
def localCycle00098 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 24 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 3c3df8940b779e46a7d51e799464e2e1a242bfc09bc458a55214b105e7b8a085.
def localCycle00099 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 0, 0, 2, 0, -2, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true, true, false] }
  origin := ![.gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 12 0]

-- Cycle fingerprint 3d3b7be79afaacfa2e5d2f1d62911cfd9b4aa46a04bb8439efb8fcca8d274fa0.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6]
    constant := ![-1, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2]

-- Cycle fingerprint 3edb8521c47701035681469d1821dc7ea26748689386038bef952d693a1cca33.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 4, .distance 0 1, .theta 1]
    constant := ![1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 16 2, .triangle 22 0, .triangle 28 0, .gapLower 4 1, .triangle 2 1, .gapLower 1 0]

-- Cycle fingerprint 3f36ec0732468952064714f42d190641646f6ef22aa43fe93ff8591da13cf1ef.
def localCycle00102 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4]
    constant := ![0, 0, -3, 0, 0, 0, 3, -1, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false, true, true, false] }
  origin := ![.gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 12 0]

-- Cycle fingerprint 40bfa11b75872f79d35bfcd2eff9f036e976d3b9e4322cfa26da9dc37db85368.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 2 6, .distance 3 6, .distance 5 6]
    constant := ![-1, 3, 0, -1, -3, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 18 1, .triangle 27 1, .triangle 33 1]

-- Cycle fingerprint 415f9647493b0f538b43926c705581747936ca73fc2479242242c7e3eb3669d3.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 5 0, .gapLower 0 1]

-- Cycle fingerprint 41c041df2122677f931ac8951d367d0dd7426e0173b3d044b1cad0aa9ec53fe8.
def localCycle00105 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6]
    constant := ![-1, -3, -1, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 21 0, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2]

-- Cycle fingerprint 41de3557ab8a97e595823cf8822e6912222b2d4c676e55324945f55de6b6688f.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 4208fff27a5697ae3ed8d0b9cc077bb551f1dbd911b945a802bd2958fbe1a9fa.
def localCycle00107 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 423b9c6436d2621562ea8a61d74652f0faa931161f042b1b86be26d32c970913.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 18 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint 425b12973da886791758743e68e4949a5af90127048b144074481420221af3ca.
def localCycle00109 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 42cc1e4bb069f97b639438bc12b5a03d3b8a4b3941bf2f482ba573c49db559f7.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 5 0, .gapLower 0 1]

-- Cycle fingerprint 430a8de9c74b539bc4d963037677638bab26f17f8db0b3c1e6b7003980a5b450.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 21 2, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 45229c13a4c4e29c1914637f7a01e5d7b6b92bb2ed1beecfb0b221a1a2dfad18.
def localCycle00112 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 1 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 22 0, .triangle 28 2, .gapUpper 2 5]

-- Cycle fingerprint 45524cc97ef5056362ca8f11cf3fe0c58f012a5cd396f410e12a6a52cce09a80.
def localCycle00113 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 459f336ef917660098e7e314e47969bc583fe9eef008a2b8d280baa8c6613b54.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5]
    constant := ![-3, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2]

-- Cycle fingerprint 45b1de3994013276beb7b9cc6ff2de9f633c3b0ecbc805e93cc178e4ab7ef8f3.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 47417737775474d59e08b18ccab4d7ec0492e3e2b6bb7b06a051d384f4190688.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint 479a2a4240b54ba514f6e1f1832ba681a94e3b068cd9449c7f6ad2f536271a29.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint 47aeecc03227f981ac1b7b98a72538c78998087b1d37a6c2674fd604788b8d32.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 485a5a323a8128af800c0ae60014c2f04301ca5d69c9c753d3c70855a766bea9.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![-1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 0, .triangle 24 0, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint 48b7463e566d8584e5b65f2f2468041354135289c00efb4454d8e49a75dbc965.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2]
    constant := ![0, -3, 0, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 18 1, .triangle 27 1, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2]

-- Cycle fingerprint 48f840445e056a49a28b70b3c2b68a7a9603f181be1c81f30a1c3a520e05a240.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 20 1, .triangle 21 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint 490668bfd64c9631385e08fa12799b1eead7e6c8e98945c5599e322a0e491996.
def localCycle00122 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 49f63891cd9e8d7b8864111a0301b20006fcd6fbe9e2a7921dd383d2cd6ad934.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4a0ad45d7f8e00ceb7a85346467493ef4e955cd76f0531e6c23a08693859c2ed.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 4a218464fa737915644043ab233bf364e0f0102fd9e4eb21638c8a61bad4a710.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![-1, 0, -1, 3, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 30 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 2, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 4a8804537d4f7df4499b24f7cb8435da8f8b2a3c5a7ba9682f43858a96d68fac.
def localCycle00126 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5]
    constant := ![-3, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2]

-- Cycle fingerprint 4b176c8d3a4578667d20d0bbc5156b3a25d29e2ffbaa60640dabe8a7b0623480.
def localCycle00127 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .gapLower 2 3, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4b4af92bba486f99b50dd895357772b0b6dd4266c5184ca53629c53cfec748dd.
def localCycle00128 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 4c5e2a48156997e79a9100136c5af051b0b5c4c21b3326383803b2d96dd3cdba.
def localCycle00129 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4c6058c82ea836ff278833e6e9276ab2e22ed749ae23244c32ee23b2bea26f51.
def localCycle00130 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 4c912e09a2a4179c20e559843ce8c5b90eed289dc29cf7cb3c5515727f957636.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 2, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint 4d3c97b5452523191ddb8cd02ced549ccef4d7fbb68b2ad08212a5ce250474bc.
def localCycle00132 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 5 4, .triangle 22 0]

-- Cycle fingerprint 4d5b39d017b42f6dcf08532014d02b738b4fc7f0a3662bb975c1ca4ee7c51fdf.
def localCycle00133 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 17 2, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 5018858cdbe62f84a8f18cdf6e9c67c44592ca1cd46987f7d23fb23caf16a72b.
def localCycle00134 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 18 2, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 5031e120fefaf5029fd53e2820eaf1f5fb5f6cf80ec7b60adbe53a9b1588cc92.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2]

-- Cycle fingerprint 51899dc7a92d20a813b3d2d81a6022cc5cfd13ad0b9c1300839711f38d88fd76.
def localCycle00136 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .distance 2 6, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 25 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 17 2, .gapLower 1 4, .triangle 18 1, .triangle 27 1]

-- Cycle fingerprint 52921440addfaf86e8b37e2a40f12ad85c96991e3fdae965b39abdadff4d53ee.
def localCycle00137 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 21 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 52c32162d1d4861ef7dc7d162b17d6680a443c01138dc62dd2f67f9764f142a2.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, 0, 0, 3, 0, -3, 0, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, true] }
  origin := ![.triangle 12 0, .gapLower 0 3, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 18 1, .triangle 27 1, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 53c0a47c0940edb7eb9673f3cf4e2ce5123287629b526e3097836fff61c22f41.
def localCycle00139 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5428b724fd05f79c5802cff3018a0483521cbf28ab36dbae58b63313a9ed4293.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 55934910b99eea73eaeefd5b2ed65129696baa6ff551b09723a6da224e3a9129.
def localCycle00141 : Cycle where
  length := 3
  data := {
    node := ![.theta 2, .theta 1, .distance 1 2, .theta 2]
    constant := ![0, 1, -2]
    coefficient := ![0, 1, -1]
    strict := ![true, false, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapUpper 2 6]

-- Cycle fingerprint 55fac8ba20bed38a61c3030bdc546f4aaa76e2f7fcc182a22ed394f6bc2fdf1e.
def localCycle00142 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 28 1, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 561f1bb32a13b31820e2507e435786669f01a879a4c9e1ae41b0936bea0e5474.
def localCycle00143 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 0, 0, -1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, false, true, false, false, false] }
  origin := ![.triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 16 0]

-- Cycle fingerprint 56e894358187601b8a71251b475217b880067d4df9f75126817b0fa990f1eee5.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 25 1, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 582d0b6567346d76f056f0cd8009b9025ae6d7ad264605c17abd24c9b13a4a14.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![3, -2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 58a3c266584270148253fb60d2c09fbca6c25a98ae8542d8ebc8ad4eb36cfc8a.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4]
    constant := ![0, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0]

-- Cycle fingerprint 5989a94c01118eccc4dfc095fcb449ea2b0829adee6d2f5515a145ae7a962a1f.
def localCycle00147 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 1 3, .distance 1 4]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 19 2]

-- Cycle fingerprint 59e723b71ca801f658cff88b530430996737a22af3f72c6a4e66899e09dc50aa.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1]

-- Cycle fingerprint 5bc94368459a44f0030d5c602d06f8f52142d51c9f1cc44122763406a5e0deb2.
def localCycle00149 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 5c74607038df0b62980fee5f191e2a52ea5723427ce3c17f0c6bd1c2b065964e.
def localCycle00150 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 5ca896964e3f70182a9cd49811c227b10757cdb8ef8c4bac93f74f526a87c906.
def localCycle00151 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5deef2772852cc58d9edd2c02913cdc9b3d779a7e70d9319ba8654e756531998.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 3, .theta 2]
    constant := ![3, -2, -2, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 16 1, .triangle 28 0, .triangle 12 0, .gapLower 0 3, .gapLower 3 0, .thetaNext 2]

-- Cycle fingerprint 5e219cb528b00100c2fdfe65bcf5e144ef5e7c77521d068b2c7eb836ccd9d921.
def localCycle00153 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 4]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 2 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 28 0, .gapLower 4 1]

-- Cycle fingerprint 5ecdb076cc5ac968f8dc1c64411aabecb72a681005fa136ccbb3856c1c2dc3ad.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 5f001a038caf6054ebe2855ab7cfb7e4a4643e9bcccb00e704cc0d318b8314e3.
def localCycle00155 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 4]
    constant := ![0, -1, 0, -1, 0, -1, 0, 0, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 1, .triangle 26 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 0]

-- Cycle fingerprint 5f6a7245e239e58274c097227106b1b0fe885072f9c9a59721b66b092f0fc767.
def localCycle00156 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .triangle 5 0]

-- Cycle fingerprint 5f93ab30f7e3049e0fa0d7e19aaace070f871b67125ba77226deb65b4d4f708d.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 5fabb4db954e057c2c818a74ad9c2d79f550387bb85cbb711a95ea1667893e79.
def localCycle00158 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .gapLower 5 3, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint 5fd267a6fb25ada86e46a455a92e54bd868a9b7446adbfdda73cf4007758ad30.
def localCycle00159 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 0, 0, 2, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, true, false] }
  origin := ![.gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 15 1, .triangle 26 0, .triangle 31 1, .triangle 12 0]

-- Cycle fingerprint 5fe643747ad66ead08adda477ade93c7976aaadce7576cbeaeae5dfb389202c0.
def localCycle00160 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 613df2d180b861db5b01f40ea363288b3332a798e0c5114c87893e4b99558368.
def localCycle00161 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 6 2, .gapLower 4 0]

-- Cycle fingerprint 61963c0bb236906cbf84736605f1964ee18ac6c73f69100e396fdb82afafdf60.
def localCycle00162 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2]
    constant := ![0, -1, 0, 0, 3, 0, -2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, true, false] }
  origin := ![.triangle 0 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 22 2, .gapLower 1 2, .triangle 15 1, .triangle 5 0]

-- Cycle fingerprint 61dcfcb9c2f2986b66a9d111a66c0f1fe297ebf0f3de64796242be9200f9dab2.
def localCycle00163 : Cycle where
  length := 4
  data := {
    node := ![.distance 5 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 5 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 33 2, .triangle 21 0, .gapLower 1 2, .gapUpper 5 5]

-- Cycle fingerprint 61de10ce297c0291aadf5fdacbc7874a16acab03cc83374946f1efc8f6e1e396.
def localCycle00164 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![-1, -1, 0, 0, -2, 0, 0, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 30 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint 62641048636de9166de107ca18805e604c63eb14ab5e0c107c45d63bcbee8a21.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, 0, 0, 3, -2, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 27 1, .triangle 26 0]

-- Cycle fingerprint 629c89657a5a430557e53e3d624c85571149347f037d89733a8ccfec3ff92dcb.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 62b5b7bfb520210bc4ed8093720c5e50b1f4d4e57b7f6e764377db594891c520.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 63f6b3df9717c09d266ac48375f9b88c7522222f07c0353c58de9898e66d233f.
def localCycle00168 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 2, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1]

-- Cycle fingerprint 64bd5d57567cdef23915eaaae806dcf07c28028324e5283522a08d066467114e.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 64e4928616c1f92e380cb48cd34acf6dfe53bc46f02ee2cdbcebab1bc835290a.
def localCycle00170 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint 65de18ae97778e4aeeeefa70ee8ae18c43a4bbd6ff104cc2608c7cb7b18e939f.
def localCycle00171 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 0 1]
    constant := ![-2, 2, -1]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .triangle 0 0]

-- Cycle fingerprint 669b32b2fd9b3ab4f6adac9e975807465823f65a53b0e087f961b73828c13077.
def localCycle00172 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 66da2de397098e18325d765806f576844a775aa90d49b3fe35800c07a799fff2.
def localCycle00173 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 67162464fb5e0785d450a831c5c841bca4b1f60d9aa906e7bc74c74f8a7dbb3e.
def localCycle00174 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 6a299b2bac2a9cbc5f6178ff6532e9e737639de1ae98b12674dd4e3c864b98ba.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 21 2, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint 6a652f4312e6f0d8a465da9f3cd4241f6df0a6dca56ff1b0d1382d2920d70b8e.
def localCycle00176 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 5]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 24 1, .triangle 30 0]

-- Cycle fingerprint 6a6f9e36f568723fc4bf9f6aa4ac4266117635ca0e0cdbaff163ee523aeca34f.
def localCycle00177 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 24 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 6a9bd400df8d8fc450cfb21ea4553f1e20f103e0e4ebcd332f5f01ee0f46e0dc.
def localCycle00178 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 15 1, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 6b0bd716451bd1b31ddb6ae7428ef5dfea2143d5c8ca347fa385470133026c9a.
def localCycle00179 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6]
    constant := ![0, -1, 3, -1, -2, -1, 2, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint 6bfccc1763449542c5aeae2e9f96672be37b52ff1fcd1140e0f2063d33cf4e56.
def localCycle00180 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 3 5, .distance 1 5]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 3 3, .triangle 20 2]

-- Cycle fingerprint 6c67051834f247c950ebc339abbd79382ecd400f7ded275a60089973dce23757.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint 6caeadadaaf3e1a7a379298acdb12850cbde48abba13b38ebbcecb7d1d3c2b0f.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 1, .theta 1]
    constant := ![2, -1, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 17 0, .triangle 30 0, .triangle 14 0, .gapLower 0 4, .triangle 2 1, .gapLower 1 0]

-- Cycle fingerprint 6cbafcce945477950bb48019e3cb5f31c2c3fa8dbc9ae061ebbca307662c71f2.
def localCycle00183 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6d06ad787746708ed2f42e640cc4e8470830bc64d572b792f627031376c035e1.
def localCycle00184 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 6d571b658709f0b40fbc8f176ffccb842aaab2469792724ddb1fd0cbb533b9a9.
def localCycle00185 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, 0, -1, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 18 1, .triangle 27 1, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint 6d677d8c6bf6454300288ac8dbe4db46184f638d01565778794da77c25a3c5b5.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 4 0, .corridorLower 0 1]

-- Cycle fingerprint 6d83ccabe2fc2b444e831be17fa95ef31ce72a091c580abf41e0232afff12732.
def localCycle00187 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 6dc26a3839b2dd53219807b957a3c7cf754eed5fbbd5914501d8909d04985313.
def localCycle00188 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, 0, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 15 1, .triangle 26 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint 6e1b383d94287d5767eac12c7d871c953ea5d1029a3a4615f79a9f7577a47f45.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 6e82883304858622287bd9925ccea9a1cf6a6473d390a6e103b83d30623eb549.
def localCycle00190 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 32 1, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 6f73467ec6f1a6df18ad39a71478c96f802a8b27b82b64817668cc0af051c022.
def localCycle00191 : Cycle where
  length := 5
  data := {
    node := ![.distance 5 6, .distance 2 6, .distance 1 2, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 30 2, .gapUpper 2 5, .triangle 17 2, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 7004a767536840e8cb2d8183b3775e0aa63b2ed848716b1a1190fdcb38dfc996.
def localCycle00192 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint 73302bd1f1e974bf13e9e1ac94daea473e6dd932eea4e9739aab4e182bb3223a.
def localCycle00193 : Cycle where
  length := 5
  data := {
    node := ![.distance 4 6, .distance 2 6, .distance 1 2, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 29 2, .gapUpper 2 5, .triangle 16 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 73beb4dea99ccfaf380707b9fbf7af9d148de2772c09e5a2cdbb6875261f2927.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint 73c48962ed2a8dab75ca0a7f87cf9e8a0ffaace6151663164c79a1ee797c6668.
def localCycle00195 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 74094a6bdc5a3374df4bbc6b89789447143c00116c99b2fd34113ecf5b4ced97.
def localCycle00196 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 4 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 4 4]

-- Cycle fingerprint 7410e3f104201e6829701831a9c96de165dfb004ca85a0f17d528205066cff05.
def localCycle00197 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, -1, 0, 0, 2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 31 1, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 18 2, .gapLower 1 4, .triangle 15 1, .triangle 26 0]

-- Cycle fingerprint 749da69e16b75100e696b68d313d628d1316f966ac86a0678517de32fa0969a5.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 7594b542407a6a97089b9564244ca0c89e0f517734189ee4472c9b51b42f4e63.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 7616dd187a30844b160207a91a0b077de8e8bc6f0d2c14c4c6394c78eee5af7e.
def localCycle00200 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, 0, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .gapLower 1 4, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint 764ada77e66765dfebe8fd1392e695d340d3c84d38d1ed9925f7a83e010f7cbc.
def localCycle00201 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, 0, -3, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 31 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 26 0]

-- Cycle fingerprint 76b24129dd07a00ba7bb0dcdee3999c2b0b809b4074eb162523e61e92a438dd3.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 7730149eb2ef3300b23bc7a15d8838bf4e256e8e5db9ece57d2cf78254274467.
def localCycle00203 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint 774b9f6325cd626402a5ce5111fc533078f041fd1d71130ff107444f0bee0448.
def localCycle00204 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 2 4]
    constant := ![0, -1, 3, 0, -2, -2, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 23 1, .triangle 29 0]

-- Cycle fingerprint 79d22e7a4b4f72575d8924ed9f4b04a323cd63649a754e8b9219cae7ff7077aa.
def localCycle00205 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -1, -1, 0, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 7a456fda9c02d6c690a576f57d79a89a33114c22b9acc1929cfd565a964c4d0b.
def localCycle00206 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 7ac11edabceb51a6882dceb6d36755c7fc16f99cde664db324ec6a484759bc18.
def localCycle00207 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 3, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 7bd2fca4c89a7ddc09652a125b18921c228d450e74023900d41955bdfdbb3356.
def localCycle00208 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 6 4, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2]

-- Cycle fingerprint 7bf973dce644437a470d1011d2be0e1f1cb2080c4b9ffb34a815700f480e99a9.
def localCycle00209 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 7d4faad445fe41469bbc796c0c57ceed04694d3088d9fda4a5d3bccaf7e15886.
def localCycle00210 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .triangle 5 0, .triangle 0 1]

-- Cycle fingerprint 7e8cc7f96c662586d5c0601dae8631f78552471f12e5bb509349d7c9239e5455.
def localCycle00211 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 2, .gapLower 1 2]

-- Cycle fingerprint 7f3682f97edf3e7144d93c3439f577aa9d67b723cc019765ef13d3e7e29899cf.
def localCycle00212 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, 0, -2, -1, 2, -1, 0, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.triangle 19 0, .triangle 21 2, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 7f38846cb8f12d6551120deb0306b6b1124c427b4774ab4dc0fca71338df0519.
def localCycle00213 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint 811732a4f758020b17e16d22f9df3b91ba7272badb3d8dd657a0814324c72123.
def localCycle00214 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 81974a403129ad27af7c47d16310418185fe507689c8dfb159286184eb80a85c.
def localCycle00215 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint 81f3a5246f5cd92061f7468c86f102ff253b40c98cf533831801d2e31e13ada1.
def localCycle00216 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 2 5, .distance 1 2]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 22 0, .triangle 28 2, .gapUpper 2 5]

-- Cycle fingerprint 8243f0965fc4f26d1354aca81a312e5c1d30218ac041bbc0bfb3c4229bed3ef3.
def localCycle00217 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5]
    constant := ![0, -1, -1, 0, 0, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0]

-- Cycle fingerprint 82769481dada0415a6bff789c67911deab66f0ffcb9e6a78b6d0284468aef4e0.
def localCycle00218 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 5, .distance 2 5, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 0, 0, 2, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 32 1, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 17 1, .triangle 26 1, .triangle 27 0]

-- Cycle fingerprint 842dd7fbc0e9b2fdaafb263455ffd671cbfb59c71a24f3bba60a3a6580b44fd0.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 2, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 84b3a91bc893ee3da6fb3871bba5ed99e9ba528963f6ca59389efef9b007c4a5.
def localCycle00220 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, -1, 0, 0, 2, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 18 1, .triangle 27 1, .triangle 26 0]

-- Cycle fingerprint 8525cc87d083300e62c58d2a277e33255e65427487b49e3611987c5974fe85cd.
def localCycle00221 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![3, -2, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 18 1, .triangle 27 1, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 85c1935f5e883ad41b8456fca1a73e5cb8d6ba7f3cd80c5fc29a65b665121f9e.
def localCycle00222 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint 8641ba6f8cc8c8b39f8cbc03c1091d0206d7e052790d33206262bf356ff24322.
def localCycle00223 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint 8646f1ea5746bf0a900a4285553d3f81c4b7cf026d3ad60f1785808d5e5d1064.
def localCycle00224 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 2 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 17 1, .triangle 26 1, .triangle 27 0, .triangle 32 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1]

-- Cycle fingerprint 864796e1e1359bf6550f0a21904eaf943591ceb6d0898ddabc75c623b7806578.
def localCycle00225 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 8758b9fafb0e8aa643aab186730953167440a5fcc0f92703a26b341dd3a0921d.
def localCycle00226 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapLower 1 4, .triangle 20 1]

-- Cycle fingerprint 88b06e12383d0b45f44c65be042d2cff94109b835df4e66d13a36b8cdda8481e.
def localCycle00227 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 890bf1531bc69373d149dbe7e74cd025e2a6807d31da75bc1f9e9acb47f70e37.
def localCycle00228 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 8d93aacc8d5c123cdb7fe618458d2857d1b71251c27e455fb5710b748c2474f5.
def localCycle00229 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![-1, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 8ddb3752651964347d3362eb1452199908ab946f7ffe36750fe26f8421c8c941.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 2, .distance 2 6, .distance 2 4, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 18 0, .triangle 29 1, .triangle 28 0]

-- Cycle fingerprint 8eccfcc437b838a2f01846c861f690243285d3c33ccf7c4cd6f1ca2f1891f6e5.
def localCycle00231 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 8f347d66e53761bc91fe7c970082a149afb8864af5ba3f94e457fc212e594a14.
def localCycle00232 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 8f579fc1f3f883c65abfae81c6b1375d56ad48d69a1e928c9289ae35cd5d3c39.
def localCycle00233 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 24 2, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2]

-- Cycle fingerprint 8fcf612409ae9ce079c4e4ce671fac16c4558efd76824a1d2ac73f97e2c456b9.
def localCycle00234 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 90095224502e644f856526409bee26ae01bab3c128514832e1ec36ab37a8ead2.
def localCycle00235 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6]
    constant := ![0, -1, 0, -1, 0, 0, 2, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 34 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint 91bc19565844ade036fd4e27b8758bde9fca52ea0e67379a95afb45bc7b71ce9.
def localCycle00236 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6]
    constant := ![0, -1, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint 91d3bf5f8bfe64c38d29a0062a88989478d12ef55e628ee769a3ea0596758fc3.
def localCycle00237 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint 92756ce6f90691be1b226b6a71a503b986a61c8499e1f421f295fe9888a467a8.
def localCycle00238 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![-1, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint 9299395381ad03266d21436831ce123948d82eba42fc8bc40cf4eecbd340d23b.
def localCycle00239 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5]
    constant := ![3, -1, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 932e7a54f9c3fc17ed2b707f2acc84e9861c2dd5e5c49111bac80d9dccdff183.
def localCycle00240 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2]
    constant := ![3, -2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .gapLower 1 4, .triangle 15 1, .triangle 26 0, .triangle 31 1, .triangle 9 0, .gapLower 0 2, .gapLower 2 0]

-- Cycle fingerprint 9440c5ab6840332372b212a9f3c46c343861857e69dba4402f58cfb54d2f87da.
def localCycle00241 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint 947cd2dff4828e071242453437ea46ef75c68e90c98cc6798a8c8839c2b55cfe.
def localCycle00242 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 94bdbda09d61c26957ce0acdb94cc9fdce6ca6d8211ecc444f46eebbf6c033de.
def localCycle00243 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 968dfa9d10f961a9f0046706a28fbeac28978f1ddbc35463622efda303289e18.
def localCycle00244 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 4, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 97061dba3fcc2cf580029519f7c7f4d745e7224c137707ee7605c705f1b3d566.
def localCycle00245 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 28 1, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 970b46a49e71969dccdb3127d6767fc2df3e1745944b78c1ba3f4f3166294dff.
def localCycle00246 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6]

-- Cycle fingerprint 98e76b9fc5a0dc26a5916ef54198df39bb27dd9763d877b2e69962582736ef03.
def localCycle00247 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 98f5d2bd7c0793ec744dbc333c229f9919eba9b7df8036ded7a1ef5403f5e5ca.
def localCycle00248 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint 98fedec86b3b18272083d022ea9ccc06ede3e3deadccda182795af359f4a27a2.
def localCycle00249 : Cycle where
  length := 5
  data := {
    node := ![.distance 4 5, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 28 2, .gapUpper 2 5, .triangle 16 2, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint 99d1cd70d39816b824312b490b15caa3763a5695aad5ffebc6e9298e8e3c0737.
def localCycle00250 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 6]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 6 5, .triangle 23 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint 9a966551bd19b9c48dbd478430497ec0cec091fbe8b4e7a84bd3462c290240a3.
def localCycle00251 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9c636b2eeb3bc0a8bdb7314c0fc61868b6b66d8cd70307f392fc44bc98a27302.
def localCycle00252 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 5 0, .gapLower 0 1]

-- Cycle fingerprint 9d29bf6e0696ff54bee9b491453b1daa09582ebc6d6acae1235ae6313660eac6.
def localCycle00253 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, 0, -2, 0, -1, -1, 0, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 16 1, .triangle 28 0, .triangle 12 0, .gapLower 0 3, .triangle 5 1, .triangle 0 1, .gapLower 1 0]

-- Cycle fingerprint 9d2b7c2e7a93be397fbd42b23b17d5936659e9100fb30f1761f198b5374841ae.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4]
    constant := ![0, -1, 0, 0, 2, -2, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 2, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .gapLower 1 5, .triangle 22 0, .triangle 28 0]

-- Cycle fingerprint 9d80fe05916d8a6bb4ae43dca5c09f6f8b4dee3099ee0711f0c37ebac97aa462.
def localCycle00255 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![-2, 0, -1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 16 1, .triangle 28 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 18 2]

-- Cycle fingerprint 9dc7bac6c7617bed825e1365ff7907f15671f76b8216ff0e429a0092d30a4f0d.
def localCycle00256 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![2, 2, 0, -1, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapUpper 5 5, .triangle 34 2, .triangle 23 0, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 9e5325ffb7215ccce384e7c33eaa3bc2267606b52e79665c11be207824785037.
def localCycle00257 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 17 1, .triangle 26 1, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9fa8aa47f21194ad1a7c2da8981e1492f8008c7a2a6ed9cc81b10fdfe6219664.
def localCycle00258 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 9fb6c980c56dd1e7650fcdbdf6a78df197f313184a60141c86628d91d58171c9.
def localCycle00259 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![-1, 0, 0, 3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, true] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .triangle 5 0, .triangle 0 1]

-- Cycle fingerprint 9fdeb658a4ec565c5092c259c6f7a8ea60ed6d90396821ea806da35c0c3bb3ea.
def localCycle00260 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -2, -2, -1, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint 9fe31e95de88d69ba152b4033dc91c7702e14497fe5724de14b051c2ed11cabd.
def localCycle00261 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, true] }
  origin := ![.triangle 23 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2]

-- Cycle fingerprint 9fe4b280c92f24eb54e5abd7c12de2ab6544e45086b10b8680c11e7a498bd8c6.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint 9ff440542488792c44abe2f963f5b6e71a19715567eb48f17d85b4c84b9c5fe9.
def localCycle00263 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 0 5, .distance 0 4, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6]
    constant := ![-3, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 3 2, .triangle 12 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3]

-- Cycle fingerprint a003a84749ece48602df121134314fa0420b360e33764373268921cf676e4d3a.
def localCycle00264 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .gapLower 1 6, .triangle 16 0, .triangle 29 0, .triangle 34 1]

-- Cycle fingerprint a02cde57ee5470eba11e6bc08660a7dc78ba95d481b5b086fdd2051217d015d3.
def localCycle00265 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .triangle 33 2, .triangle 21 0]

-- Cycle fingerprint a05faa4cba0286962d2c4ba58c50fdeba18755230ed43bd378e4f93c6a68efa1.
def localCycle00266 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint a098858af14a2bf330507fa3ab5e68074e13a578afe660ca8c22da937a3fef48.
def localCycle00267 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a0e98fa595dc11ee3dcc2964bd53ecb421992c3801b3f8e1d8f37ed4503004cc.
def localCycle00268 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 2 3, .triangle 26 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a1df84ae5a480ad622c884bf74fa324be7b9c81fe576b906bf66c638c639b4ad.
def localCycle00269 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a2379ad037b0463d46e5c64105bb4494982483de45de354fcc41a10627aa452a.
def localCycle00270 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint a2ef511ab6bd370d560ba8fafbf679f87291bc0faa30d0a0aa5c333a11c9c375.
def localCycle00271 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint a421436ee2a3e8e86379375bc401789d005120aa069acb8e68235c8c34aaa032.
def localCycle00272 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, 0, 0, 3, 0, -2, -2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, true] }
  origin := ![.triangle 12 0, .gapLower 0 3, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 15 1, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint a4f92db99d01c5f146eaab8c359a0b784a756fbd14285d5de880895032cc05cb.
def localCycle00273 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0]

-- Cycle fingerprint a6a32800c0d29f62dbeb82dc62653ee5ba1640d44b915d6f17307f3ce952a4dc.
def localCycle00274 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 5 5, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint a7c084ec464fbe849289909dbdeb4579e761a0061934c3ea715661a7e0ba084b.
def localCycle00275 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint a84f735e6768f55aacd2068f0b2f2f30dd733f1c169436c9c479aae523a1640e.
def localCycle00276 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint a8a974d64aa1435eeba36ded052c1ab451db56010af071023112f24b5f656bb9.
def localCycle00277 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 15 1, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint a8e949f63df8cb1702afa8f6587eef8363eb28eeb948c96abb66e4ff77dd8659.
def localCycle00278 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![0, -2, -2, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint a930409d953adbb1823eeda0c6dea6413b0da231debf6ec24532e345e3b22bcc.
def localCycle00279 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3]
    constant := ![-2, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0]

-- Cycle fingerprint a9b981870b15a9ecf282c044d4f9fbc4ced794888dd294c287eb7ebe462243e0.
def localCycle00280 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 5 4, .triangle 22 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint aa044c742ead9342de58b1e5b49ff0570d5d367898f397e14a5c9b48848b0fee.
def localCycle00281 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 1 2, .distance 1 5]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 17 2]

-- Cycle fingerprint aa5d8fc73799c4f6f43937a126a31f7ed78df362071661fecbbc35838eb60c34.
def localCycle00282 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint aae44c2a6d1f347cffc4049fc3369c1f5d0106081006cc2bfb791025648fe1ec.
def localCycle00283 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint abc5ec9299306bf114e86669cfd136254219edcdb924ce3125636cd81090ae06.
def localCycle00284 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 22 0]

-- Cycle fingerprint abf42161645a9dd044edee6ddd457810b1242d2a909e834e36afd3f96fe2593e.
def localCycle00285 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0]

-- Cycle fingerprint abf4e6aaa081becc089bfbf7b567f10d5e2e819c7a38342129efe7bd1ef01cfb.
def localCycle00286 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint ac5853d4f673f27035138f76f99e36c60e1b4f06ed83f86c242ac363f122375d.
def localCycle00287 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 3 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 3, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint ac63858f3405cc256e61c4819b2774f7602cc4684f9bf5ae68e3cce2fcc99651.
def localCycle00288 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint ac9dbced26c9859ac2a121c08a03873a0ee43666c23dbe47cab5727a0863590e.
def localCycle00289 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint acfbd926c76052ae2a9a2a19b6cb1b64a80a0985d31c0fa6fcd70fc52db9a912.
def localCycle00290 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.triangle 25 0, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 15 1]

-- Cycle fingerprint ad84e992d12c601d8aef6f91070aa08c78028c10c27823d83680ee55d004fe11.
def localCycle00291 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 1 4, .distance 1 3, .distance 3 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 4 5, .gapLower 1 4, .gapUpper 3 5]

-- Cycle fingerprint aedea93da46a65e7b170df6ddd2e245a323f0dc61622cd3831c5da1bcf63ad8a.
def localCycle00292 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 1 2]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 23 0, .triangle 29 2, .gapUpper 2 5]

-- Cycle fingerprint b1809648447db3ea5e4b2c2e0a50d9a920133bf7dae9c4e5024fb099c82ffdc2.
def localCycle00293 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 0, 0, 2, 0, -2, 0, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, true, false] }
  origin := ![.gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 18 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .triangle 12 0]

-- Cycle fingerprint b181896f736ee5b52c1652f1119559bc9cfce0d721943be0bd75ebb0f521d6e5.
def localCycle00294 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![0, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 5 3, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint b2258e091407d8f87f336eb34bf2078d8f38bca77dd80f5d5e91e7f68999b22a.
def localCycle00295 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint b301bbf4a5f52ee1ed31092102f30e865257f0812989b04f1d41ed658b79db12.
def localCycle00296 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 5, .gapLower 1 5, .triangle 18 1]

-- Cycle fingerprint b3260865f4f3316a887447e2f6cedc28b3b8a9de53d9c6b1a21bbb36871d38cc.
def localCycle00297 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint b3c3302b4ace24d96de395e73118b127b242961a60dad7d7c2e7e763cbbc99b2.
def localCycle00298 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 2, .distance 1 4, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 1]
    constant := ![2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 1]

-- Cycle fingerprint b3f526d2b4bb859e48cfee7d0de07c558f0d9017bd1d7c1d37a6f5e5b40e193a.
def localCycle00299 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 19 1, .gapLower 1 3, .triangle 4 0]

-- Cycle fingerprint b4f3fdfb4b6af6fcd4fd23649ea0ce9e65ae0c53a78240cf95fa327be7db8d8d.
def localCycle00300 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 2 2, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint b530ca181000d395fec88dbbc3238a8b014abb8ee54cbe0242bdda6ae076577c.
def localCycle00301 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 5]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, false, true] }
  origin := ![.gapLower 5 4, .triangle 22 0, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint b55353d36984c5b0ed3a319f9936958b46d9b30f069cdcf1ae17e9053127f1ca.
def localCycle00302 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 5]
    constant := ![0, -1, 0, -1, 0, 0, 2, -2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 31 1, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 16 1, .triangle 25 1, .triangle 26 0]

-- Cycle fingerprint b5907bf1721a33dd4b4237736967fd3cd829fdc1d34846c2a8ef5ec876a97fe9.
def localCycle00303 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint b612a762f27b8e4b41e15c2ca5b3d487c1890b5139d21cc171fae1b0e8821426.
def localCycle00304 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 4 5, .distance 2 5]
    constant := ![-1, 0, 0, -1, 0, 0, 2, 0, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 30 0, .gapLower 5 1, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 2, .gapLower 1 4, .triangle 22 1, .triangle 28 2]

-- Cycle fingerprint b6a58d5c44dd572499f6711dc928a618e6f6c385eed4183b473ef7553a1aef59.
def localCycle00305 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint b705f8300bbac20d79cf6738584d91420e32dfcb6c6b03c3b8111917b048881a.
def localCycle00306 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, -1, 0, -1, 0, 0, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 15 1, .triangle 26 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2]

-- Cycle fingerprint b855e33a09ce86d7ff501a6ce37ccd4fa61b449f8a03968850065274bb8ae76b.
def localCycle00307 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint b94351ae4a8257e7a5d263f5af79040167e9469530fc5b52fea3eca95a357053.
def localCycle00308 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 3, .distance 3 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 5, .gapLower 1 2, .gapUpper 3 3]

-- Cycle fingerprint b9c29007a7a164d16f5b0aa64d3d635e58dbd422c95a190600cc8e79414c5feb.
def localCycle00309 : Cycle where
  length := 6
  data := {
    node := ![.theta 0, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint ba0d83ded1e1c5c50290195697efc990bf958aca5e3db86fff69833438e10a0f.
def localCycle00310 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 23 0]

-- Cycle fingerprint baa2c21691fb6467a46c8d51960e36e95d3fe469df6d349fed9dce7b4ef06946.
def localCycle00311 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 1 4, .triangle 3 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint bb24bfb52eb657457465b9ca1d2ae8bce56fbc84c60eb4636e2463c95ed82b72.
def localCycle00312 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint bc25f4269afffa3624fe911b3f64257a9ec5423d72b21dbec3cce70cb1f3f011.
def localCycle00313 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 32 0, .triangle 29 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint bd226e0c629ad0797a9bae6805b15a478cc526faab269775dbe6bc49bd1d1f09.
def localCycle00314 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4]
    constant := ![3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint be458680f865fb51e0f49b1d8646ca2b5d01f0ae9a8deebd909bbccd70b51e72.
def localCycle00315 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint befeea78a22b5da7cc8bd6f5e14cf11dffd62d3508ecb5d3d5d1187c80539511.
def localCycle00316 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint bf34313b7ae585059aba07df6114a947cb08e218d1c68d013b55ee8bdc86dd01.
def localCycle00317 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 3, .corridorUpper 1 2]

-- Cycle fingerprint bf4b4eabf4cdaf052d46aca41818bc53e220a168f0c9fcb57e08c80bca4be151.
def localCycle00318 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 5, .gapLower 1 5, .triangle 17 1]

-- Cycle fingerprint bf8f9c1f7df307cbc31c5c109e355b5f4e5dfb7920f6235896b6d3930aebe222.
def localCycle00319 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, 0, -1, 0, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 1 4]

-- Cycle fingerprint c187e8e013e561930139c48feea8512fcf821678b3cce0c7699ff5fc4873f1ad.
def localCycle00320 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 23 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint c20bb7a4d3469978e1814e2acbe473ba1e232579e2c924125a67cec623ade233.
def localCycle00321 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, 0, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 16 1, .triangle 25 1, .triangle 26 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1]

-- Cycle fingerprint c3f487f2d5ca031e1e45d083bcf11681b2787248a21492fe598ad4b2ccc013bf.
def localCycle00322 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint c3fd8164e987bddffd4f595c33ea128ea21e13f7ce778fde9a501d59602220e5.
def localCycle00323 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint c44756e5b13bc3e7ab74c4d1866876fcbad20afcbd2fdfc42bdb7976c13f35bb.
def localCycle00324 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint c44c067dc3a0d7748d9ecdb335d6dc3fe63c5ad8cd0bad51c52a57083fbcbd7f.
def localCycle00325 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![0, -3, -1, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint c509b1e07c8de41f56154914ba0c3af49c564f0f59050e59e533035dd8726c31.
def localCycle00326 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 16 2, .gapLower 1 4, .triangle 24 2, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint c555ef359831451260f1e02aa521afe8ffcc1361c3278e3b334369c2dadbaba5.
def localCycle00327 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 0, .triangle 28 0, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c580eb741dd8ff97b99541354baf25da0af15cbc6654d9df08c3d8bbb8dfc2cd.
def localCycle00328 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint c597f235b9ec9c5b5e2d2dd25844070d6c5e7f4d35d8433dc8dd7e8029c5b175.
def localCycle00329 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint c59b2ae221131ca1c0fa787476e152d6e1b6b6c46409865dae1374feab273c13.
def localCycle00330 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, 3, -1, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint c81bff3a4af1d86b238d238ee9d85bb38610ee110d1d9ad536244cdcffcebf76.
def localCycle00331 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint c8da447125de360d10cb956b7ff25c111a91e25b9813df29409736f7d4b098f2.
def localCycle00332 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .triangle 9 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint c9db98d88400aeac7db7d26497e6ee5e6cff1a4b293531b5add0a63b226f4608.
def localCycle00333 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 2 6, .distance 2 4, .distance 4 5, .distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 6]
    constant := ![0, 0, -1, -1, 0, -1, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 18 1, .triangle 29 1, .triangle 28 0, .triangle 12 0, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint cc4f6a732c6fd94c801da2bb8a32121e399e36abd2875d04c16011ae415d4084.
def localCycle00334 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 6, .distance 1 4, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, 0, -2, -1, 2, -1, 0, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true, false, true, false, false, true] }
  origin := ![.triangle 20 0, .triangle 21 2, .gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint cd26af610dbb7e7f5abfd6a24dc1e65bd1c8b345e75ff2a654e87df7f07d7b7b.
def localCycle00335 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint cd6949d567b2295063cd83c0ad325753dc9529171faa22da0a9b3a01d71c98f5.
def localCycle00336 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint ce42d1ec757a5e256a8f5f8ccc64c09e09335e54678120dfabece3173307d513.
def localCycle00337 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3]
    constant := ![-1, 0, -2, 0, 0, 3, -2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 5 0, .gapLower 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2]

-- Cycle fingerprint ce74a2d7a80120e706723469464bc66a77d0fdfd442951ecca346927bb57c3aa.
def localCycle00338 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 0 4]
    constant := ![0, 0, -2, 0, 0, 3, -2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 16 1, .triangle 29 0, .triangle 34 1, .triangle 12 0]

-- Cycle fingerprint ceca543f0dcca6529696c113005b45be2d4c061a337988f993d8d894b36ee046.
def localCycle00339 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 5, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint cee643d2db74fb9f6be9d9a6a2910ce0d716edd4bda9b28ecaf47f3c8f861d0d.
def localCycle00340 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint cf4b09b41e8d469fd5f0b71f0a3e842e8b4ccee565b3a2f473116dc45209f878.
def localCycle00341 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, -1, -1, 0, 0, -3, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint cf8208ea209c9085140f56b733afc9b5a28006596e8e7de6154ae8dc30649464.
def localCycle00342 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .triangle 19 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint cfc0408014d11a712c9822878b32b5f540992f0a17d05ad38eac8e1fdafc9ebb.
def localCycle00343 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .gapLower 1 4, .triangle 4 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d19187cdc50313c48ece799a32a0c2f10609ef26530c41e8ddd0d4be7b2cb75f.
def localCycle00344 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d2666dd4ec83606a6ebf73546899001b855d82824db28ddd89b0028731656922.
def localCycle00345 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint d26eb5061c3a9a79273d2ce930d8aec99af376b0837f72c27f93421fbfd1d9b6.
def localCycle00346 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 4]
    constant := ![0, -1, 0, -2, 2, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 25 1, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 18 0, .triangle 30 1, .triangle 28 1]

-- Cycle fingerprint d5049b8fa1f00e41bf10f633c692a7cbce879e89d2dd6edf8d21409e3237c816.
def localCycle00347 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 1 3, .distance 2 3, .distance 3 4, .distance 0 3, .distance 0 2, .theta 2, .distance 1 2]
    constant := ![0, -2, -2, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .gapLower 1 3, .triangle 15 1, .triangle 25 0, .triangle 9 0, .gapLower 0 2, .gapLower 2 0, .corridorUpper 1 2]

-- Cycle fingerprint d547e6b3d76f53685c6d071155068985196852f51dc8fa696c1720510952fd1a.
def localCycle00348 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint d5f40763bb168e318e78b818383954500ffe3337ad609bf91b101a596794b4df.
def localCycle00349 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 2, .distance 0 2, .distance 0 1, .theta 1, .zero]
    constant := ![0, 2, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.thetaUpper 2, .gapUpper 2 0, .triangle 0 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d63796fff61d507bb5f65e85ca47f7c1cf0a78875d9667784cf0219d50522003.
def localCycle00350 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 20 2, .gapLower 1 2, .triangle 2 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint d72fa2b98ac2eb860c1fbf5aa54667a2f16e1d261ac0af944ee882b6b04ae6e6.
def localCycle00351 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint d7931389e17c9d43bffce3a8910c86c057142abee0570370220cce04a3d09979.
def localCycle00352 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint d825317d8ae4ce0ff6694cd03c1757fee1b70aca9cc4c381dd003ce024682af6.
def localCycle00353 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 18 2, .gapLower 1 4, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1]

-- Cycle fingerprint d8c2358c626e5eea153d1d91547ed75a747ca8baf681d2977c947cf5b2dbae2a.
def localCycle00354 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, -1, 0, 0, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1]

-- Cycle fingerprint d967b4869fecf9f6845802ad4100552f22e5638beab30f14a95435dbf29eb6fa.
def localCycle00355 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint d9b490ae15c4ed10c80dd06853f04da26db025438d3d00ccd3f5e1e3bf4571f8.
def localCycle00356 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint d9b82c445a0f7a63d5bc0e21d72fd87dbc1004ae0096c8136f25caf9a7bcbe35.
def localCycle00357 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 5 0, .gapLower 0 1, .gapLower 1 0, .thetaNext 0]

-- Cycle fingerprint da0f6305222bc8ac7e44e13aa686251b9312585ebeaf487763fe983f4899867d.
def localCycle00358 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 0 1]
    constant := ![-2, 0, 0, 3, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint da4e9d9a4e3591d9192a13e1375f96133caa27410e8460f7f9f98c90dc3634c2.
def localCycle00359 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 20 2, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint db6ef3889b55eb491eacd52aebb80f08a779003398017fdd5201365495b4595b.
def localCycle00360 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 2 5, .distance 3 5]
    constant := ![0, -1, 3, -1, -2, -2, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, true] }
  origin := ![.triangle 31 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 3, .gapLower 1 2, .triangle 17 1, .triangle 26 1]

-- Cycle fingerprint dbdf8e8b577f97fa36d84f1f96a545d6197f0861b72ed892b054f8e5d23957f8.
def localCycle00361 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 1, .corridorLower 0 1]

-- Cycle fingerprint deb1f55ba4bd2bd35ec112b5567fc119f8e882ae46544e58f4c39d5b7c721215.
def localCycle00362 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 1 5]
    constant := ![-1, -1, 0, 0, 3, 0, 0, -1, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 3 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .gapLower 1 3]

-- Cycle fingerprint deb9d1ce1e2c8987fabc56948571d601297651d675ee9e03243563c8106bc8d5.
def localCycle00363 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Cycle fingerprint df855051e1c97bd482208ee5ace152a0a7b1e34a84cddb9d8fe31569cdea32a2.
def localCycle00364 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint e031c7daa302223b6e911ab67c86db8e30dbb847d2227016d791777fa712783e.
def localCycle00365 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 24 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint e11325426596589b4dc2ae67badea501ef2f9bbb43ccc5de6685b887dbf05fd7.
def localCycle00366 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, 0, -1, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint e11f9bf8af1831fe90a05bd3d91b20514bd51f6ab25ed49f051086b8ad2f94ef.
def localCycle00367 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 0 1, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 17 2, .triangle 24 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint e1a68970e4bad34ec968816c9dc32817f7edd74936d94e4ea9ecc213420cdca1.
def localCycle00368 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 3, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e244521a55a43a674d54ba366c596d09973fe6ec7d5a007ecc11abec71bfe704.
def localCycle00369 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5]
    constant := ![-2, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2]

-- Cycle fingerprint e28bfa5722664a1c8360e1382aca6ee0221aa7d93beea383034dc21e40795df7.
def localCycle00370 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 4]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 0, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 22 0, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 2]

-- Cycle fingerprint e2e7000ecc0af58d15c6ad2a7bd77eb25f765ce418497f07ce1fef91057cedaa.
def localCycle00371 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 4, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 22 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint e31cd20ac8a54d1eefce3219478e06ab846a5ba96bb6fcda5299633ee15eca88.
def localCycle00372 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 1 4]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 22 0]

-- Cycle fingerprint e3e6f2e53dbbd573aaa3ad844eaa190904d29aca492521f845b1498aa2728b4c.
def localCycle00373 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 5, .distance 1 3, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 0, 0, 2, 0, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.triangle 32 1, .triangle 9 0, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 17 2, .gapLower 1 4, .triangle 15 1, .triangle 27 0]

-- Cycle fingerprint e453da6aa5fccb9e97f3eab0541e1bc95a9d759528a958d3d3ed808485a8e6d5.
def localCycle00374 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e5e95cf4bb708fdc1898b9018206ad0459a5466a1454d6902bc1d722596d614f.
def localCycle00375 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 4]
    constant := ![-1, -1, 0, -1, -1, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 32 0, .triangle 23 0, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 0]

-- Cycle fingerprint e71d02aa8f936ed1a17f46b11e48ec4b044b1e6ae60e2dabc59ea955dc607f36.
def localCycle00376 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1]
    constant := ![0, 0, 0, 3, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e71d2a5bea8699e7982515f1d061000eeed3cdbad9a65f0264062612f906adee.
def localCycle00377 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 5, .triangle 24 0, .triangle 30 2, .gapUpper 2 5]

-- Cycle fingerprint e836966a218ac023aeb483f0d274e47069b6f03a08594103177f2d656d4a5088.
def localCycle00378 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint e8cc1e235c0358f3a3b088656320dfa9a540338aae36b1a4c7f5ab48455d3bd1.
def localCycle00379 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint e981d5c252197d9a2574b72029690c57b29217a604904740e18d85f7ff7a4cea.
def localCycle00380 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![-1, -1, 0, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint e991a9bce320ac911fae8d4bbfcd2d43e0c18f58b61cdf3166f342c493194f3a.
def localCycle00381 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![-1, -3, 0, 0, 3, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint e9e326c259aac1483b9b6d93160550c608ed3cc8ea4d3c583f260f09456be2d5.
def localCycle00382 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 1 3, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 22 2, .triangle 24 2, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint ea7c36866b3d03c32223bf8aa19b04286b092ca1f5cf2b268491a0a271fa80ae.
def localCycle00383 : Cycle where
  length := 11
  data := {
    node := ![.theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![0, 0, 3, 0, -1, 0, -2, 0, -2, -1, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .gapLower 6 3, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1]

-- Cycle fingerprint eab7ca1c92a77833364d7e18d86d7ebf6bad84ecfee8aa1da8bc6458400f9176.
def localCycle00384 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 4, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 23 1, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint ebfd76ae3e3adaa1042c1224826199d9c7587106ee3e9890481b485b314add19.
def localCycle00385 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 0 1, .theta 0, .zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3]
    constant := ![-3, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 20 0]

-- Cycle fingerprint ed33b964f9147ed4b2cd4e75546cda30ab16b2c0cf14779fa1ae591a0264fbda.
def localCycle00386 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ed627ba8c7a7790f18feaf773dcb09ea44d7937ba59b1d55558519e504254b08.
def localCycle00387 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4]
    constant := ![-1, 0, -1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 14 0, .gapLower 0 4, .corridorLower 0 4, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .triangle 16 2]

-- Cycle fingerprint edafea539b42b206123bf74a2e4923ffbe21c357208850addf8cdc007350a74b.
def localCycle00388 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint ef1422c527f95926ec1b573e68cb45dabbe328bb7c649b8d07987fc310d64097.
def localCycle00389 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 24 1, .gapLower 1 2, .triangle 2 0]

-- Cycle fingerprint f04f61890bf2990d89e72b5117b836de9a9ecc7065fa2f69e2314e5902195936.
def localCycle00390 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 1 3]
    constant := ![-2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 4 4, .gapLower 6 5, .triangle 21 0]

-- Cycle fingerprint f1b661909597334606cc70b1223ef8b6089bfd184e1158c6f134482073a03562.
def localCycle00391 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 2]
    constant := ![3, 0, -2, 0, 0, -1, 0, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .gapLower 1 4, .triangle 18 1, .triangle 27 1, .triangle 26 0, .triangle 31 1, .triangle 12 0, .gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2]

-- Cycle fingerprint f1f6979c1dfd20bf07e4d1d4bcf1fc8b9d0975994eac90adb18552d8497f05e8.
def localCycle00392 : Cycle where
  length := 14
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![-2, 0, -1, 0, 0, -1, 0, 0, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 15 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 12 0, .gapLower 0 3, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint f52e226d11ba56e72285a6144a6aa914479ad0285c4f75c445831dc17ee857b9.
def localCycle00393 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint f531d5c1f61b10d3b1146d79bf095c48646e954cd386bdfc33f3fbb3689a7616.
def localCycle00394 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 6, .distance 2 6, .distance 5 6, .distance 0 6, .distance 0 4, .theta 4, .distance 3 4, .distance 4 5]
    constant := ![0, -3, 0, 0, 0, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.gapLower 5 4, .gapLower 1 4, .triangle 18 1, .triangle 30 1, .gapLower 6 1, .triangle 13 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 31 0]

-- Cycle fingerprint f64cc9db9496f7e40ad14b22424c7a1a6aa3a8eb449c10d7fe9399b81cdcce29.
def localCycle00395 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![0, -2, 0, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 17 2, .gapLower 1 4, .triangle 23 1, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint f67a04328da11dd289efab297221fa7098c6a54d82e746fa98b77391a1c81e3d.
def localCycle00396 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 3 6, .distance 1 6]
    constant := ![-2, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapUpper 3 3, .triangle 21 2]

-- Cycle fingerprint f81b39ba09838c2a3e62a3734bd9b6232fbb566d2cbe34728ae967e50728e604.
def localCycle00397 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 6, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 1 4]
    constant := ![0, -2, -1, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 22 2, .gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 16 2]

-- Cycle fingerprint f881bb50dc797b002b2c22edde4e29a02ae5d925eeaaafa66414e80a0aadd78b.
def localCycle00398 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 20 1, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint f896482514e425ec30deab1195523434ec7a3f0f62c895b4f97e792466896251.
def localCycle00399 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6]
    constant := ![-1, 3, 0, -1, -2, -1, 2, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, true] }
  origin := ![.corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1]

-- Cycle fingerprint f8a820dbaba506fa45e17a939d45c5292e7d97cd315e9743209be98aa33b55b5.
def localCycle00400 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 4, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 6 2, .gapLower 4 0]

-- Cycle fingerprint f95f39cfaa4d1a9543d43c3a3c327aa79648ce624d9c7d295f9e0a36ef0f71e6.
def localCycle00401 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 6, .distance 0 1, .theta 0, .zero, .theta 2, .distance 1 2]
    constant := ![-2, -2, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2]

-- Cycle fingerprint f9d98cc6efcd710320f1ac47fee71d6f2345ffea9769bb159e85f8eb551d7e2d.
def localCycle00402 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 1 3]
    constant := ![-2, -1, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 4 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 19 0]

-- Cycle fingerprint fb6bde98508b4e8588b4c4ec339492c12090121ed9c5eecc73bc4e34b2992294.
def localCycle00403 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 4, .distance 0 3, .theta 0, .zero, .theta 1, .distance 1 2, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 0 4]
    constant := ![0, -1, 0, 0, 2, -2, 0, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true, true, false] }
  origin := ![.gapLower 0 3, .corridorLower 0 3, .thetaLower 0, .thetaUpper 1, .gapLower 1 6, .gapLower 1 5, .triangle 16 1, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 12 0]

-- Cycle fingerprint fc02bb9bb7145eac7e56caaec55f388dcb7f577d80db4737ef95b90fa88cf3c7.
def localCycle00404 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 0 1, .theta 0, .zero, .theta 2]
    constant := ![3, -2, 0, 0, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0, .thetaUpper 2]

-- Cycle fingerprint fc3b4792351d4460ae0cc339acf212451a5e162b07cabafda0dc39af7939d8b5.
def localCycle00405 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fc441bb643445e03e9d3545717f308396463f65381847c8f20eab276557104a0.
def localCycle00406 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -2, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0]

-- Cycle fingerprint fd230dfed9510385af7cbea56e1ccff3e49576fbb5fdffd37448285663315c4c.
def localCycle00407 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fd89e8a67205ac0fda036012beea0c5cb14eca8f41d86837fb3e77bfaf73497d.
def localCycle00408 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 3, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6]
    constant := ![-1, -2, -1, -2, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 23 0, .gapLower 1 2, .triangle 1 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2]

-- Cycle fingerprint feaf82394c0c2c1a3247a136407523d5c767081b5e05dbd8425b84b6a9905800.
def localCycle00409 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Cycle fingerprint fecc4bce6f3db79dd2d1444f6c8eaf239498c388cd2d87eed0f5f78d0a012022.
def localCycle00410 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4]
    constant := ![-1, 0, 0, -2, 2, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .gapLower 1 6, .triangle 17 0, .triangle 26 1, .triangle 25 0]

-- Cycle fingerprint fee0b77e2ba9aaf3eede1099aadc784764eafcf468b317e7e3708fedcfdf146d.
def localCycle00411 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 0 1, .theta 1, .zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6]
    constant := ![0, -2, -1, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 6 4, .gapLower 1 3, .triangle 3 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0]

-- Cycle fingerprint ff1fc919c34efca62ffbe715533afe28c31ef5c23e7f60bebcc0bcb01845ff9f.
def localCycle00412 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 4, .distance 0 3, .distance 0 1, .theta 1, .zero, .theta 2, .distance 1 2, .distance 1 6, .distance 2 6, .distance 2 4, .distance 4 5, .distance 0 4]
    constant := ![0, 0, -2, 0, 0, 3, -2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 0 3, .triangle 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 2, .corridorUpper 1 2, .gapLower 1 5, .triangle 18 1, .triangle 29 1, .triangle 28 0, .triangle 12 0]

-- Cycle fingerprint ffba90a2f493253a1686da3e286b5afc28c37290d25c3d70ed7f3a53ac01ee81.
def localCycle00413 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 1, .theta 0, .zero, .theta 2, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, 0, -3, 0, 0, 0, 3, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 32 1, .triangle 9 0, .gapLower 0 2, .triangle 0 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 2, .corridorUpper 1 2, .triangle 17 0, .triangle 26 1, .triangle 27 0]

def library : Library := fun id => if id < 207 then (if id < 103 then (if id < 51 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 38 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))))) else (if id < 44 then (if id < 41 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)))) else (if id < 47 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))))) else (if id < 77 then (if id < 64 then (if id < 57 then (if id < 54 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))) else (if id < 70 then (if id < 67 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))) else (if id < 73 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))))) else (if id < 90 then (if id < 83 then (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)))) else (if id < 86 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))))) else (if id < 96 then (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)))) else (if id < 99 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))) else (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)))))))) else (if id < 155 then (if id < 129 then (if id < 116 then (if id < 109 then (if id < 106 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 112 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))) else (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))))) else (if id < 122 then (if id < 119 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none))) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))) else (if id < 125 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)))))) else (if id < 142 then (if id < 135 then (if id < 132 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)))) else (if id < 138 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))) else (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))))) else (if id < 148 then (if id < 145 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none))) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)))) else (if id < 151 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none))) else (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))))))) else (if id < 181 then (if id < 168 then (if id < 161 then (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)))) else (if id < 164 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))) else (if id < 166 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))))) else (if id < 174 then (if id < 171 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)))) else (if id < 177 then (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))) else (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)))))) else (if id < 194 then (if id < 187 then (if id < 184 then (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none))) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)))) else (if id < 190 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))) else (if id < 192 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id = 191 then some localCycle00191 else none)) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none))))) else (if id < 200 then (if id < 197 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)))) else (if id < 203 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))) else (if id < 205 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none))))))))) else (if id < 310 then (if id < 258 then (if id < 232 then (if id < 219 then (if id < 213 then (if id < 210 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none)))) else (if id < 216 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none))) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none))))) else (if id < 225 then (if id < 222 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none))) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)))) else (if id < 228 then (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id = 227 then some localCycle00227 else none))) else (if id < 230 then (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)) else (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id = 231 then some localCycle00231 else none)))))) else (if id < 245 then (if id < 238 then (if id < 235 then (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none))) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none)))) else (if id < 241 then (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none))) else (if id < 243 then (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id = 242 then some localCycle00242 else none)) else (if id < 244 then (if id = 243 then some localCycle00243 else none) else (if id = 244 then some localCycle00244 else none))))) else (if id < 251 then (if id < 248 then (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none))) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none)))) else (if id < 254 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id < 253 then (if id = 252 then some localCycle00252 else none) else (if id = 253 then some localCycle00253 else none))) else (if id < 256 then (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none)) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none))))))) else (if id < 284 then (if id < 271 then (if id < 264 then (if id < 261 then (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id = 260 then some localCycle00260 else none))) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id = 263 then some localCycle00263 else none)))) else (if id < 267 then (if id < 265 then (if id = 264 then some localCycle00264 else none) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none))) else (if id < 269 then (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none)) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none))))) else (if id < 277 then (if id < 274 then (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none))) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none)))) else (if id < 280 then (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none))) else (if id < 282 then (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none)) else (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id = 283 then some localCycle00283 else none)))))) else (if id < 297 then (if id < 290 then (if id < 287 then (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id = 286 then some localCycle00286 else none))) else (if id < 288 then (if id = 287 then some localCycle00287 else none) else (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id = 289 then some localCycle00289 else none)))) else (if id < 293 then (if id < 291 then (if id = 290 then some localCycle00290 else none) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id = 292 then some localCycle00292 else none))) else (if id < 295 then (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id = 294 then some localCycle00294 else none)) else (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id = 296 then some localCycle00296 else none))))) else (if id < 303 then (if id < 300 then (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id = 299 then some localCycle00299 else none))) else (if id < 301 then (if id = 300 then some localCycle00300 else none) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id = 302 then some localCycle00302 else none)))) else (if id < 306 then (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id = 305 then some localCycle00305 else none))) else (if id < 308 then (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id = 307 then some localCycle00307 else none)) else (if id < 309 then (if id = 308 then some localCycle00308 else none) else (if id = 309 then some localCycle00309 else none)))))))) else (if id < 362 then (if id < 336 then (if id < 323 then (if id < 316 then (if id < 313 then (if id < 311 then (if id = 310 then some localCycle00310 else none) else (if id < 312 then (if id = 311 then some localCycle00311 else none) else (if id = 312 then some localCycle00312 else none))) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id < 315 then (if id = 314 then some localCycle00314 else none) else (if id = 315 then some localCycle00315 else none)))) else (if id < 319 then (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id < 318 then (if id = 317 then some localCycle00317 else none) else (if id = 318 then some localCycle00318 else none))) else (if id < 321 then (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none)) else (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id = 322 then some localCycle00322 else none))))) else (if id < 329 then (if id < 326 then (if id < 324 then (if id = 323 then some localCycle00323 else none) else (if id < 325 then (if id = 324 then some localCycle00324 else none) else (if id = 325 then some localCycle00325 else none))) else (if id < 327 then (if id = 326 then some localCycle00326 else none) else (if id < 328 then (if id = 327 then some localCycle00327 else none) else (if id = 328 then some localCycle00328 else none)))) else (if id < 332 then (if id < 330 then (if id = 329 then some localCycle00329 else none) else (if id < 331 then (if id = 330 then some localCycle00330 else none) else (if id = 331 then some localCycle00331 else none))) else (if id < 334 then (if id < 333 then (if id = 332 then some localCycle00332 else none) else (if id = 333 then some localCycle00333 else none)) else (if id < 335 then (if id = 334 then some localCycle00334 else none) else (if id = 335 then some localCycle00335 else none)))))) else (if id < 349 then (if id < 342 then (if id < 339 then (if id < 337 then (if id = 336 then some localCycle00336 else none) else (if id < 338 then (if id = 337 then some localCycle00337 else none) else (if id = 338 then some localCycle00338 else none))) else (if id < 340 then (if id = 339 then some localCycle00339 else none) else (if id < 341 then (if id = 340 then some localCycle00340 else none) else (if id = 341 then some localCycle00341 else none)))) else (if id < 345 then (if id < 343 then (if id = 342 then some localCycle00342 else none) else (if id < 344 then (if id = 343 then some localCycle00343 else none) else (if id = 344 then some localCycle00344 else none))) else (if id < 347 then (if id < 346 then (if id = 345 then some localCycle00345 else none) else (if id = 346 then some localCycle00346 else none)) else (if id < 348 then (if id = 347 then some localCycle00347 else none) else (if id = 348 then some localCycle00348 else none))))) else (if id < 355 then (if id < 352 then (if id < 350 then (if id = 349 then some localCycle00349 else none) else (if id < 351 then (if id = 350 then some localCycle00350 else none) else (if id = 351 then some localCycle00351 else none))) else (if id < 353 then (if id = 352 then some localCycle00352 else none) else (if id < 354 then (if id = 353 then some localCycle00353 else none) else (if id = 354 then some localCycle00354 else none)))) else (if id < 358 then (if id < 356 then (if id = 355 then some localCycle00355 else none) else (if id < 357 then (if id = 356 then some localCycle00356 else none) else (if id = 357 then some localCycle00357 else none))) else (if id < 360 then (if id < 359 then (if id = 358 then some localCycle00358 else none) else (if id = 359 then some localCycle00359 else none)) else (if id < 361 then (if id = 360 then some localCycle00360 else none) else (if id = 361 then some localCycle00361 else none))))))) else (if id < 388 then (if id < 375 then (if id < 368 then (if id < 365 then (if id < 363 then (if id = 362 then some localCycle00362 else none) else (if id < 364 then (if id = 363 then some localCycle00363 else none) else (if id = 364 then some localCycle00364 else none))) else (if id < 366 then (if id = 365 then some localCycle00365 else none) else (if id < 367 then (if id = 366 then some localCycle00366 else none) else (if id = 367 then some localCycle00367 else none)))) else (if id < 371 then (if id < 369 then (if id = 368 then some localCycle00368 else none) else (if id < 370 then (if id = 369 then some localCycle00369 else none) else (if id = 370 then some localCycle00370 else none))) else (if id < 373 then (if id < 372 then (if id = 371 then some localCycle00371 else none) else (if id = 372 then some localCycle00372 else none)) else (if id < 374 then (if id = 373 then some localCycle00373 else none) else (if id = 374 then some localCycle00374 else none))))) else (if id < 381 then (if id < 378 then (if id < 376 then (if id = 375 then some localCycle00375 else none) else (if id < 377 then (if id = 376 then some localCycle00376 else none) else (if id = 377 then some localCycle00377 else none))) else (if id < 379 then (if id = 378 then some localCycle00378 else none) else (if id < 380 then (if id = 379 then some localCycle00379 else none) else (if id = 380 then some localCycle00380 else none)))) else (if id < 384 then (if id < 382 then (if id = 381 then some localCycle00381 else none) else (if id < 383 then (if id = 382 then some localCycle00382 else none) else (if id = 383 then some localCycle00383 else none))) else (if id < 386 then (if id < 385 then (if id = 384 then some localCycle00384 else none) else (if id = 385 then some localCycle00385 else none)) else (if id < 387 then (if id = 386 then some localCycle00386 else none) else (if id = 387 then some localCycle00387 else none)))))) else (if id < 401 then (if id < 394 then (if id < 391 then (if id < 389 then (if id = 388 then some localCycle00388 else none) else (if id < 390 then (if id = 389 then some localCycle00389 else none) else (if id = 390 then some localCycle00390 else none))) else (if id < 392 then (if id = 391 then some localCycle00391 else none) else (if id < 393 then (if id = 392 then some localCycle00392 else none) else (if id = 393 then some localCycle00393 else none)))) else (if id < 397 then (if id < 395 then (if id = 394 then some localCycle00394 else none) else (if id < 396 then (if id = 395 then some localCycle00395 else none) else (if id = 396 then some localCycle00396 else none))) else (if id < 399 then (if id < 398 then (if id = 397 then some localCycle00397 else none) else (if id = 398 then some localCycle00398 else none)) else (if id < 400 then (if id = 399 then some localCycle00399 else none) else (if id = 400 then some localCycle00400 else none))))) else (if id < 407 then (if id < 404 then (if id < 402 then (if id = 401 then some localCycle00401 else none) else (if id < 403 then (if id = 402 then some localCycle00402 else none) else (if id = 403 then some localCycle00403 else none))) else (if id < 405 then (if id = 404 then some localCycle00404 else none) else (if id < 406 then (if id = 405 then some localCycle00405 else none) else (if id = 406 then some localCycle00406 else none)))) else (if id < 410 then (if id < 408 then (if id = 407 then some localCycle00407 else none) else (if id < 409 then (if id = 408 then some localCycle00408 else none) else (if id = 409 then some localCycle00409 else none))) else (if id < 412 then (if id < 411 then (if id = 410 then some localCycle00410 else none) else (if id = 411 then some localCycle00411 else none)) else (if id < 413 then (if id = 412 then some localCycle00412 else none) else (if id = 413 then some localCycle00413 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 4, 5, 6], ![0, 2, 1, 3, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 262 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 640)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 4, 5, 6], ![0, 2, 1, 3, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 157 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 641)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .low (![48, 117, 207, 85, 70, 296, 141, 279, 406, 53, 275, 358, 346, 355, 366, 226, 199, 239, 303, 383, 213, 409, 36, 118, 118, 206, 319, 229]) }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 642)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 6, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .low (![349, 117, 207, 283, 282, 49, 141, 6, 372, 367, 191, 377, 171, 123, 91, 191, 377, 239, 259, 395, 377, 330, 148, 377, 281, 377, 133, 80]) }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 643)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 4, 6, 5], ![0, 2, 1, 3, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .low (![79, 117, 207, 283, 126, 318, 141, 6, 372, 367, 42, 164, 182, 123, 91, 33, 398, 239, 259, 55, 140, 330, 148, 26, 281, 401, 133, 8]) }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 644)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 4, 3]], proof := .tail 217 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 645)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 6, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 4, 3]], proof := .tail 245 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 646)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 6, 4, 5], ![0, 2, 1, 6, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 4, 3]], proof := .tail 375 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 647)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 4, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 4, 5], ![0, 2, 6, 1, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 4, 1, 3]], proof := .tail 231 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 648)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 4, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 6, 4, 5], ![0, 2, 6, 1, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 4, 1, 3]], proof := .tail 231 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 649)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 1, 6, 4, 5], ![0, 6, 2, 1, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 4, 2, 1, 3]], proof := .tail 223 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 650)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 5, 4, 6], ![0, 2, 1, 5, 3, 6], ![0, 2, 1, 4, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 205 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 651)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 5, 6, 4], ![0, 2, 1, 5, 6, 3], ![0, 2, 1, 4, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .low (![381, 325, 132, 158, 263, 296, 141, 228, 305, 294, 311, 358, 346, 260, 280, 2, 199, 386, 180, 354, 301, 301, 13, 312, 40, 206, 134, 229]) }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 652)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 5, 6, 3], ![0, 2, 1, 4, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 380 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 653)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![0, 2, 1, 6, 4, 3], ![0, 2, 1, 5, 4, 3]], proof := .tail 119 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 654)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 6, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![0, 2, 6, 1, 4, 3], ![0, 2, 5, 1, 4, 3]], proof := .tail 269 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 655)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 4, 6, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 1, 6, 5, 3], ![0, 6, 2, 1, 4, 3], ![0, 5, 2, 1, 4, 3]], proof := .low (![35, 146, 310, 378, 394, 318, 141, 376, 408, 208, 343, 164, 182, 100, 320, 58, 398, 405, 396, 64, 250, 250, 278, 26, 281, 401, 133, 8]) }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 656)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 4, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 6, 1, 5, 3], ![0, 2, 6, 1, 4, 3], ![0, 2, 5, 4, 1, 3]], proof := .tail 130 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 657)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 4, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 6, 1, 5, 3], ![0, 6, 2, 1, 4, 3], ![0, 5, 2, 4, 1, 3]], proof := .tail 130 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 658)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 4, 5, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 1, 6, 5, 4], ![0, 6, 2, 1, 5, 3], ![0, 6, 2, 1, 4, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 129 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 659)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 5, 4, 6], ![0, 2, 5, 1, 3, 6], ![0, 2, 4, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 122 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 660)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 5, 6, 4], ![0, 2, 5, 1, 6, 3], ![0, 2, 4, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 161 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 661)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 5, 1, 6, 3], ![0, 2, 4, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 400 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 662)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 6, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 5, 6, 4], ![0, 2, 5, 6, 1, 3], ![0, 2, 4, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .low (![349, 385, 244, 60, 187, 292, 141, 286, 31, 276, 193, 17, 171, 5, 22, 193, 17, 356, 210, 227, 17, 128, 29, 17, 339, 17, 20, 62]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 663)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 6, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 5, 6, 1, 3], ![0, 2, 4, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 107 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 664)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 5, 6, 1, 3], ![0, 2, 4, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 172 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 665)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 6, 5, 1, 3], ![0, 2, 6, 4, 1, 3], ![0, 2, 5, 4, 1, 3]], proof := .tail 270 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 666)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 1, 6, 5, 4], ![0, 2, 6, 5, 1, 3], ![0, 6, 2, 4, 1, 3], ![0, 5, 2, 4, 1, 3]], proof := .low (![153, 309, 308, 77, 345, 216, 101, 368, 233, 397, 249, 112, 171, 135, 328, 249, 112, 387, 266, 326, 112, 382, 204, 112, 170, 112, 304, 254]) }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 667)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 1, 6, 5, 4], ![0, 6, 2, 5, 1, 3], ![0, 6, 2, 4, 1, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 315 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 668)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 5, 4, 6], ![0, 5, 2, 1, 3, 6], ![0, 4, 2, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .low (![370, 246, 244, 256, 84, 296, 141, 47, 31, 73, 253, 412, 230, 23, 297, 342, 199, 285, 238, 162, 189, 211, 353, 384, 236, 152, 255, 333]) }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 669)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 5, 6, 4], ![0, 5, 2, 1, 6, 3], ![0, 4, 2, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 38 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 670)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 5, 2, 1, 6, 3], ![0, 4, 2, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 0 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 671)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 5, 6, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 2, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 39 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 672)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 2, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 109 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 673)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 6, 5, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 2, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 234 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 674)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 5, 6, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 2, 1, 3, 6], ![0, 4, 2, 1, 3, 5]], proof := .low (![74, 385, 244, 388, 4, 86, 141, 286, 31, 92, 329, 338, 264, 5, 22, 361, 404, 356, 210, 156, 56, 128, 181, 1, 339, 248, 298, 19]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 675)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 2, 1, 6, 3], ![0, 4, 2, 1, 5, 3]], proof := .low (![341, 273, 89, 352, 4, 86, 141, 374, 365, 411, 329, 338, 264, 323, 98, 361, 404, 83, 379, 177, 177, 177, 181, 1, 339, 248, 298, 19]) }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 676)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 2, 6, 1, 3], ![0, 4, 2, 5, 1, 3]], proof := .low (![349, 309, 308, 52, 237, 86, 141, 368, 233, 14, 357, 337, 171, 135, 328, 184, 50, 110, 266, 184, 50, 382, 176, 125, 170, 317, 104, 252]) }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 677)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 1, 6, 5, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 6, 2, 1, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 37 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 678)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 1, 6, 5, 4], ![0, 6, 5, 2, 1, 3], ![0, 6, 4, 2, 1, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 327 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 679)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 1, 4, 5], ![0, 2, 6, 1, 3, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 335 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 680)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 1, 4, 5], ![0, 2, 6, 1, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 139 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 681)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 5, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 4, 2, 3, 1]], proof := .tail 139 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 682)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 3], ![0, 2, 6, 1, 4, 3], ![0, 2, 5, 4, 3, 1]], proof := .tail 267 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 683)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 1, 5, 4], ![0, 2, 6, 1, 5, 3], ![0, 6, 2, 1, 4, 3], ![0, 5, 2, 4, 3, 1]], proof := .tail 267 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 684)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 5, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 1, 5, 4], ![0, 6, 2, 1, 5, 3], ![0, 6, 2, 1, 4, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 183 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 685)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 1, 5, 4], ![0, 2, 5, 6, 1, 3], ![0, 2, 4, 6, 1, 3], ![0, 2, 4, 5, 3, 1]], proof := .tail 300 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 686)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 1, 5, 4], ![0, 2, 6, 5, 1, 3], ![0, 2, 6, 4, 1, 3], ![0, 2, 5, 4, 3, 1]], proof := .tail 106 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 687)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 1, 5, 4], ![0, 2, 6, 5, 1, 3], ![0, 6, 2, 4, 1, 3], ![0, 5, 2, 4, 3, 1]], proof := .tail 267 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 688)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 1, 5, 4], ![0, 6, 2, 5, 1, 3], ![0, 6, 2, 4, 1, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 41 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 689)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 6, 1, 5, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 2, 6, 1, 3], ![0, 2, 4, 5, 3, 1]], proof := .tail 336 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 690)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 1, 5, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 2, 6, 1, 3], ![0, 4, 2, 5, 3, 1]], proof := .tail 247 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 691)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 1, 5, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 6, 2, 1, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 82 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 692)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 1, 5, 4], ![0, 6, 5, 2, 1, 3], ![0, 6, 4, 2, 1, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 106 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 693)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 1, 4, 5], ![0, 6, 2, 1, 3, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 364 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 694)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 4, 5, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 1, 5, 4], ![0, 6, 2, 1, 5, 3], ![0, 6, 2, 1, 4, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 322 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 695)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 1, 5, 4], ![0, 6, 2, 5, 1, 3], ![0, 6, 2, 4, 1, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 315 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 696)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 6, 2, 1, 3], ![0, 4, 5, 3, 2, 1]], proof := .tail 61 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 697)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![0, 6, 5, 2, 1, 3], ![0, 6, 4, 2, 1, 3], ![0, 5, 4, 3, 2, 1]], proof := .tail 327 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 698)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 1, 4, 6], ![0, 2, 5, 1, 3, 6], ![0, 2, 4, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 173 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 699)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 1, 6, 4], ![0, 2, 5, 1, 6, 3], ![0, 2, 4, 3, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 214 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 700)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 6, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 1, 6, 4], ![0, 2, 5, 6, 1, 3], ![0, 2, 4, 3, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 209 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 701)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 3, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 6, 1, 4], ![0, 2, 5, 6, 1, 3], ![0, 2, 4, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 115 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 702)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 5, 6, 1, 4], ![0, 2, 5, 6, 1, 3], ![0, 2, 4, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 331 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 703)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 5, 1, 4], ![0, 2, 5, 6, 1, 3], ![0, 2, 4, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 81 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 704)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 3], ![0, 2, 6, 4, 3, 1], ![0, 2, 5, 4, 3, 1]], proof := .tail 174 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 705)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 3], ![0, 6, 2, 4, 3, 1], ![0, 5, 2, 4, 3, 1]], proof := .tail 348 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 706)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 5, 1, 4], ![0, 6, 2, 5, 1, 3], ![0, 6, 2, 4, 3, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 94 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 707)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 5, 1, 4], ![0, 6, 2, 5, 1, 3], ![0, 6, 2, 4, 3, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 198 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 708)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 1, 4, 6], ![0, 5, 2, 1, 3, 6], ![0, 4, 2, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 173 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 709)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 1, 6, 4], ![0, 5, 2, 1, 6, 3], ![0, 4, 2, 3, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 214 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 710)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 6, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 1, 6, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 2, 3, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 209 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 711)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 1, 6, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 209 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 712)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 3, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 6, 1, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 2, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 316 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 713)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 96 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 714)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 6, 1, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 2, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 331 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 715)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 6, 5, 1, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 2, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 81 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 716)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 331 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 717)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 5, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 81 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 718)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 407 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 719)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 1, 4], ![0, 6, 5, 2, 1, 3], ![0, 6, 4, 2, 3, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 295 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 720)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 6, 2, 3, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 16 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 721)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 1, 4], ![0, 6, 5, 2, 1, 3], ![0, 6, 4, 2, 3, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 198 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 722)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 1, 4, 6], ![0, 5, 2, 1, 3, 6], ![0, 4, 3, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 393 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 723)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 1, 6, 4], ![0, 5, 2, 1, 6, 3], ![0, 4, 3, 2, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 32 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 724)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 6, 4, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 1, 6, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 3, 2, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 268 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 725)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 1, 6, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .low (![75, 114, 265, 11, 138, 86, 141, 369, 271, 306, 391, 321, 168, 274, 288, 154, 15, 155, 95, 274, 274, 163, 272, 76, 159, 165, 293, 302]) }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 726)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 3, 4, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 6, 1, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 3, 2, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 225 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 727)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 225 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 728)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .low (![102, 21, 160, 25, 291, 86, 141, 314, 169, 402, 392, 51, 143, 340, 72, 167, 63, 235, 360, 10, 12, 212, 90, 299, 179, 68, 99, 403]) }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 729)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 6, 1, 4], ![0, 5, 2, 6, 1, 3], ![0, 4, 3, 2, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 166 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 730)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 3, 2, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 166 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 731)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 65 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 732)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 144 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 733)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 1, 4], ![0, 5, 6, 2, 1, 3], ![0, 4, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 81 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 734)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 1, 4], ![0, 6, 5, 2, 1, 3], ![0, 6, 4, 3, 2, 1], ![0, 5, 4, 3, 2, 1]], proof := .tail 9 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 735)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 1, 5, 6], ![0, 2, 3, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 194 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 736)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 1, 5, 6], ![0, 2, 3, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 307 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 737)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 87 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 738)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 6, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 149 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 739)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 6, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 1, 6, 5], ![0, 2, 3, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 149 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 740)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 3, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 6, 1, 5], ![0, 2, 3, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 190 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 741)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 3, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 6, 1, 5], ![0, 2, 3, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 190 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 742)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 6, 1, 5], ![0, 2, 3, 6, 1, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 67 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 743)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 6, 4, 1, 5], ![0, 2, 6, 3, 1, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 4, 3, 1]], proof := .tail 142 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 744)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 4, 6, 1, 5], ![0, 2, 3, 6, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 67 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 745)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 3, 4, 6, 5, 1], ![0, 2, 6, 4, 1, 5], ![0, 2, 6, 3, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 4, 3, 1]], proof := .tail 313 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 746)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 3, 6, 4, 5, 1], ![0, 2, 6, 4, 1, 5], ![0, 6, 2, 3, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 4, 2, 3, 1]], proof := .tail 363 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 747)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 6, 3, 4, 5, 1], ![0, 6, 2, 4, 1, 5], ![0, 6, 2, 3, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 78 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 748)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 1, 5, 6], ![0, 3, 2, 1, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 71 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 749)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 1, 5, 6], ![0, 3, 2, 1, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 178 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 750)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 5, 6, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 257 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 751)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 6, 5, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 127 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 752)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 3, 6, 5, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .low (![45, 151, 203, 147, 120, 318, 141, 97, 219, 277, 185, 164, 410, 390, 34, 66, 371, 88, 137, 390, 390, 390, 347, 46, 290, 221, 136, 8]) }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 753)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 3, 5, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 6, 1, 5], ![0, 3, 2, 1, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 1, 4]], proof := .tail 332 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 754)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 3, 5, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 6, 1, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 332 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 755)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 6, 3, 5, 2], ![0, 4, 6, 3, 5, 1], ![0, 4, 6, 2, 1, 5], ![0, 3, 2, 1, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 3, 2, 1, 4]], proof := .low (![413, 7, 196, 103, 222, 318, 141, 261, 175, 324, 200, 224, 131, 116, 28, 111, 59, 44, 232, 24, 121, 334, 186, 30, 399, 145, 373, 218]) }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 756)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 3, 4, 1]], proof := .tail 202 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 757)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 4, 3, 6, 5, 1], ![0, 4, 2, 6, 1, 5], ![0, 3, 2, 6, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 3, 4, 1]], proof := .tail 289 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 758)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 4, 6, 3, 5, 1], ![0, 4, 6, 2, 1, 5], ![0, 3, 2, 6, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 3, 2, 4, 1]], proof := .tail 251 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 759)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 1], ![0, 4, 6, 2, 1, 5], ![0, 3, 6, 2, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 3, 4, 2, 1]], proof := .tail 258 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 760)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 6, 4, 3, 5, 2], ![0, 6, 4, 3, 5, 1], ![0, 6, 4, 2, 1, 5], ![0, 6, 3, 2, 1, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 4, 3, 2, 1]], proof := .tail 57 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 761)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 1, 6], ![0, 2, 3, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 344 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 762)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 6, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 1, 6], ![0, 3, 2, 1, 5, 6], ![0, 2, 3, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 150 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 763)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 1, 6], ![0, 3, 2, 1, 5, 6], ![0, 3, 2, 1, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .low (![201, 284, 43, 105, 287, 296, 141, 195, 27, 54, 188, 18, 108, 69, 93, 359, 124, 215, 3, 350, 389, 242, 241, 192, 362, 240, 197, 220]) }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 764)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 6, 2], ![0, 3, 4, 5, 6, 1], ![0, 2, 4, 5, 1, 6], ![0, 2, 3, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 351 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 765)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 6, 2], ![0, 4, 3, 5, 6, 1], ![0, 4, 2, 5, 1, 6], ![0, 3, 2, 1, 6, 5], ![0, 2, 3, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 113 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 766)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 4, 5, 6], ![0, 4, 5, 3, 6, 2], ![0, 4, 5, 3, 6, 1], ![0, 4, 5, 2, 1, 6], ![0, 3, 2, 1, 6, 5], ![0, 3, 2, 1, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 243 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 767)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (640 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 640 ≤ id.val) (hhigh : id.val < 768) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 640)) = true := by
  let j : Fin 128 := ⟨id.val - 640, by omega⟩
  have hsum : 640 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (640 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard005
