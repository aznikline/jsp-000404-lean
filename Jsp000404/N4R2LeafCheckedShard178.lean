import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard178
open N4R2RowDataReplay

-- Original cycle 009b3d5bdeb00dcea6c8cbca812818ebf672adcbb289545e1dcf2b6194dde097; original global index 56.
def localCycle00000 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 3 5, .triangle 11 2, .gapLower 0 3]

-- Original cycle 01bb361c7bab4f340d2128a5ef537bea3304835ae0a7d5fe20178e182c827326; original global index 139.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 02970da1b774065cf1ec73fca55b31c264b5a4ddbe71556b95f5081faa17ad5a; original global index 202.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 02bdf589c8f99ac880b66cf05867feb476ca9525d8db9a6e47efeeb23fd17bba; original global index 215.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 05f62b40fb12b34bb1aeb6f771e2902fa9e4b573955dbddfd2b38641bc2f0505; original global index 496.
def localCycle00004 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 0afa1ef754accf0237e4c7f9aebbdb63986148548119eb6eb5a6955778705628; original global index 876.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 0c23045eebd258aa9d6989537b79bdc997bffc0f268cb35657404b9eb7612788; original global index 961.
def localCycle00006 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 0 6, .distance 0 3]
    constant := ![0, -2, 2, 0, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false] }
  origin := ![.triangle 10 2, .gapLower 0 1, .gapUpper 4 4, .triangle 13 2, .gapLower 0 3]

-- Original cycle 0d04c60d3e4bbe8cf70a50cb7f90cca06ea40755c1390f9482aafd05ab57b8e4; original global index 1030.
def localCycle00007 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0e4d7d98ba43e0c793a3872d386ac0d69226a83a26abb42d40f18782c1cd9940; original global index 1125.
def localCycle00008 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, -2, -2, 3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .gapLower 6 1, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3]

-- Original cycle 1258a0439888f56110b61b7f193d9aa2dd568bdf96e80366e483ce4c4889b42d; original global index 1456.
def localCycle00009 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 131da00e94f8528bc12515e3cb212c911f07f9700e23b8e7440ae89503f15352; original global index 1510.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 137a9e295e6ad2127f22ee8eb439d5d45ad2e558029cd6b613ddfe061587db70; original global index 1534.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 17419ff98a26e84c8eafa7d11588f4c123f53e25c24f34e3d2f83ffa09c10f73; original global index 1829.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 199e430a25ad87c7a0e0b9dbefb5a8223e6e453e1aa3208d6c7f1c60704cd731; original global index 2002.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 19d3f770e9da253d595229f759c8d2168586043d6c7941652e022d276a279ffb; original global index 2014.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 25 0, .triangle 19 0, .gapLower 1 2, .triangle 17 0, .corridorLower 2 5]

-- Original cycle 1c1774f08931cda8a92825ebb59e2a7fa7c05f161ec764cefde7a9d88c33d4ec; original global index 2167.
def localCycle00015 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 1c767322427585e8a1f07cf10bee65166edc6c64e0d8a129337ba0fbea4ec121; original global index 2184.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 1d06efaebd49b765f7c93e2857f11dbf752a7c2c91c5dd81cd79695db0319ac7; original global index 2237.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 22aa364e28e465e2b35b25aefc97b58b9affa975dd4e8fe868f99bb2e683c601; original global index 2657.
def localCycle00018 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .triangle 16 0, .triangle 28 2, .corridorLower 2 5]

-- Original cycle 2378c8470fa434fcf77eabf8eebb0683471d2ba083de8ce91cb3fbc3744f9b13; original global index 2720.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 23da399e1c236b12192b7a2c4fdafa57473505d3ffaa04c8665c6d80bf7b25e2; original global index 2747.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 11 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 240ec00e9cfe2a27f6c64079da866184f266f96f8979bcdf43712b8dbddc42ad; original global index 2762.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 26732450d54df7c4e4910aef061ed968e2ce9de7dbd5c784727d54309af64dbb; original global index 2951.
def localCycle00022 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -2, 3, -2, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3]

-- Original cycle 28479225313d6b451a678620d1195a343af73f68ab0e36c5d56489a0055d5f31; original global index 3087.
def localCycle00023 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2ccbaded0c451b7ac124079460d19912be5de9b8b521465137a789709b3772d7; original global index 3421.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .triangle 21 1, .triangle 19 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1]

-- Original cycle 30406780557f7d32cb80e076280f7ef8fb6cbb40ac2c37e8f191ea50d3c686a4; original global index 3672.
def localCycle00025 : Cycle where
  length := 3
  data := {
    node := ![.theta 0, .distance 0 1, .theta 1, .theta 0]
    constant := ![1, -2, 0]
    coefficient := ![1, -1, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 6, .gapUpper 1 6, .thetaNext 0]

-- Original cycle 34ecd5c7fbe50e06693853dd3d32021a249cdf4db393a7639c81903fed379278; original global index 4051.
def localCycle00026 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 6, .distance 1 6, .theta 1]
    constant := ![3, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 2, .gapLower 6 2, .corridorLower 1 6]

-- Original cycle 36594dc2bf253caeaff8aa2cc0b523af604af8e3e42d02f6abc3d9e6880536d7; original global index 4169.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 386f838a2b1d4f3d4645d5e2c093d0aa0f1ad4e3a1b15c4361476221cbbf63ae; original global index 4341.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 38753099b587af188344db66051f1958cf691b1d4a0ac55e377f80a0fd183353; original global index 4345.
def localCycle00029 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .triangle 15 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00030 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 3c6300deae1c60f2d5fa171be5d36996312708f7594701f7b52b67e78d97ad0d; original global index 4681.
def localCycle00031 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3d12fadb7a2cff0bf1ebce41fec662544731e48a28eef34f6f2b9ac0adb42ba0; original global index 4734.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 3eff3b8e4db3afce94be8c344e107479f68bdb0bc5d05bdc7733cbbe7e1642a0; original global index 4870.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .triangle 21 1, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 405c34923ea2719a5a3eff96c0c38d9d36d3d029ca570a0dad5de18edc278e1a; original global index 4975.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .triangle 16 0, .corridorLower 2 4]

-- Original cycle 4323c6c31ba78419177f351923976744817144d666cc0547af9b1b1b5579230a; original global index 5183.
def localCycle00035 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0]

-- Original cycle 43d131548851583f7268c72f69baf58def3f122b4db70b5878b507c9fa1bbbe5; original global index 5249.
def localCycle00036 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 463d40c3a8d35bf36f90b50ffed328e13cfcc2935ec65f1d8170052b1eb8aa38; original global index 5435.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 19 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 46cb37d17507150788e4bc97824951a297d83b74f6491872d150e1bf7abf3949; original global index 5486.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4866fd9848de2e1dbdbcf9ea38b33541d2c931ed3d49e52d4fe2f88de67b4f42; original global index 5605.
def localCycle00039 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 0, .gapLower 1 3, .triangle 19 2, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 4f58cb45e614ca875b86c94c8826f09148459240032fc1c1b51b80b0834f3372; original global index 6167.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -3, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .gapLower 6 1, .triangle 30 1, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 50ec246a6737ce5535e58dafa644c167751aca85e256e9caa015682e5bb635af; original global index 6286.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 53ed92fd9343a61e194ccc5f181798f3a00ec7a6e242ca4d813a201f7588d897; original global index 6510.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5566e7a7d60bb2a0973868f24d1e359206c425832dd103da9191af7443e87adb; original global index 6615.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .gapLower 1 3, .triangle 19 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 58b82f8bb1de8120efdf7024abf8b71807f3aec695c7500838cfeba924514a59; original global index 6884.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 26 1, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5995eb82af51853e671377030d3af4fe26cfe1a4be065f3f95a1c5451479a515; original global index 6964.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .thetaNext 1]

-- Original cycle 5a8e15feacf71d0b33d34b9dd701aa7255d856cba0d538637f34252e827af461; original global index 7050.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 5aa9f17edd08e7394e80b22a873d16d2121f0757f2e656b50934bf16a6198298; original global index 7057.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 5b97e417b17352a78216cc26ed1906e0273e5b35b70ed852645f43b478ad4a0d; original global index 7123.
def localCycle00048 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 0, .gapLower 1 3, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 5ebce2f8d8b6b787969c1e663c6337e232306d19640c835ac508ce8f1bdc6531; original global index 7373.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 624efdcb6ebd88bf6bd329d87d5ca41b541c3d219faa7db0bbe25b4b15403ab4; original global index 7673.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 62a84935f0880397bda29fe288e4f8a2bd72fabfdbb9e23f49e6a52cedead3fd; original global index 7699.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 636bfe3ea983153b37ed6f2582d6c79844febce1c7141a337e1592d868bf6b63; original global index 7758.
def localCycle00052 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6520e524084118997b690bf601bfbf50bdca399d8453d22071dfaf8b7625b357; original global index 7868.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .gapLower 1 3, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 65efcd5a76a2c3e04ddef720156cefdb135c02677fee36f50773a467d3d311be; original global index 7931.
def localCycle00054 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 2, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 683cdc94be63044c68cc074f2436826c8291ef5de7451e07f2554dff999d7d6e; original global index 8108.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 68621500b7cb74ec11ab090dc83e4c671c401611917cd478b5879c146b82111b; original global index 8118.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 6af47c65eeb1991e63ac623be277c198bd5e0c14eeee78326d453cde34c88890; original global index 8330.
def localCycle00057 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 6ca863f2673d6ca4c440ec70db5c448ae6e0d78e9f6f90694815e94e3e1bc26d; original global index 8452.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .gapLower 0 4, .gapLower 0 3, .gapLower 3 4, .triangle 15 2, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 70834c59e898205eb1ce481b60ffd5071dbbe61daff1a112ceaabe451ee17f80; original global index 8717.
def localCycle00059 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 783404191d177fa7996c778cb856f3c6aecc9ebb83ec3933d6d74711db8143b4; original global index 9290.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7850c537800de02de91aa086649765a8eb1a273393e8fb6c92bc2310671828c6; original global index 9300.
def localCycle00061 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 2 6, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 2 6, .thetaLower 2]

-- Original cycle 7dd0b8c5bc9df07e9917c6fc94085292d9543cf623fc8398cf55dbea4dba5309; original global index 9769.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 20 0, .triangle 19 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 7dfc7e146614a9ccd591e474b3dd290a8d62e7aa84f6762d03260ab01edd77c9; original global index 9785.
def localCycle00063 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![-3, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false] }
  origin := ![.gapLower 0 2, .triangle 12 1, .gapUpper 4 4, .triangle 32 2, .triangle 11 0]

-- Original cycle 81d36d08554c18a2411938562312b00868bb79427d4e673e79f9132e014eaed0; original global index 10077.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 88047559910629a07896af910e5b1053bcb2ff5dd941c28602785dd35213b7ae; original global index 10545.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .triangle 15 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 8a1623e246f5046cd13fda3ebe00edecc56f2183577ff0f35f4f7438ddd0134c; original global index 10702.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8aa6e074f6340b2d3eb777ce29a293e50f2be47684141282a5285f6bec3cf347; original global index 10741.
def localCycle00067 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![-2, 0, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false] }
  origin := ![.gapLower 0 2, .triangle 12 1, .gapUpper 4 4, .triangle 32 2, .triangle 11 0]

-- Original cycle 8ad7546e4162b4e7d73b24eba046ba88e00d4e251aeda8b8cc10d7c507377cad; original global index 10758.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle 8b9ce4474cf6c50a135fd5b68925fd02b88aa2d9fb777fee3e9662e6ba9703ed; original global index 10810.
def localCycle00069 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8cedba197060e14f1b8242265cd107aaf305a111f35e5d5f74d227c237db7793; original global index 10901.
def localCycle00070 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 8da163356be6df69c5305d7d4bf6dacfaddc5a5f601fdff2c5a5e8a62edf61d7; original global index 10952.
def localCycle00071 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 8 1, .gapUpper 2 5]

-- Original cycle 8ef2fd4b49c93f9e788cbd2c45c85cc78cf0dde08022864e82740ba63a2eb0a3; original global index 11057.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 9059579bed0b87e3e417b34b452dae82838b286eda163ce93ec96a7756c57ea3; original global index 11177.
def localCycle00073 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .theta 2, .theta 1]
    constant := ![3, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 2 6, .thetaNext 1]

-- Original cycle 923e5d4a9a089a305fffaaea4c59fb87d413b5c7f411134a2d0a201650b7a7ce; original global index 11326.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -2, 0, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .gapLower 0 4, .triangle 8 1, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 92423a0eb35fbf9045dc963a750726440be37509300c91cfb0d81872aac9ce2c; original global index 11329.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 0, .triangle 12 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 932c74aaaabd6280064f239dbdca38c9f44636b4b0347f8647174337626bf4e9; original global index 11411.
def localCycle00076 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9509938bf6cd20eb805bd5dc8b16e67b4aa5e948c68b4fbee9d2ccf5e54db47f; original global index 11572.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 6, .distance 0 5, .distance 0 4, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .gapLower 0 4, .triangle 14 1, .gapLower 0 1, .gapLower 4 3, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 95afe833a63f0f2919daa799af976d5f482c9495428655fec80e5f9873e3422a; original global index 11637.
def localCycle00078 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 6, .distance 0 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 2, .gapLower 0 3, .gapLower 3 4, .triangle 15 2, .triangle 20 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9a9b907c8e4a9ea33301266f1097b2e2d3fb2ae96a6dfce1d53fc93841f9b756; original global index 12011.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9af1b7a5f0396a5723e7666ab52aa78d4665e35c563ea11cb620f145f95ffddc; original global index 12044.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 9da9913119d0db260cd8985c5e46b5f8b4fb7ef55f9c89ee9d0dee3f90ff3f0b; original global index 12265.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 9e6f39db173067f149896728c2a93a866477c52e8f50ff53d004b84f5021db6d; original global index 12340.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9e9f339e71a4863d47ea125e037c55e07d6d6d5c012bca53b989c783456177cd; original global index 12352.
def localCycle00083 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 5, .gapLower 6 3, .triangle 11 1]

-- Original cycle a02cddacbb7c86c36ea1e026db5ffd447e434271cfb0fcb4cdb359f9d17500e9; original global index 12460.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a13c004e7091ceed617b6582ed7bb2f0550c1975fe4f44d40abf641c8219687b; original global index 12535.
def localCycle00085 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 4 4, .triangle 13 2, .triangle 14 1, .gapLower 0 1]

-- Original cycle a19ea2d427a294fb740de59dddb058514cffce9bd4623a908b9b3c4021de5d24; original global index 12568.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 1, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true] }
  origin := ![.gapLower 0 6, .triangle 0 2, .gapLower 0 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaNext 0]

-- Original cycle a8b4549ed57528f94c4851dc9314ef16f4c362df7e697c75661a8754150cbe04; original global index 13130.
def localCycle00087 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a8de46fee15b16db1a30b54bba1887a1d38958f4e9f68cba96b474ae78332c91; original global index 13146.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a91d181eedf74a673a6f9f3576ae3e2a3ab782d640e0cbb988b97f693187700e; original global index 13165.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 1 6, .thetaLower 1]

-- Original cycle a9a78e2b42906d58ee0645ddaacf2cdbd30f9febd6c16e4e31587b64cc6f922b; original global index 13208.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .corridorLower 2 4, .thetaNext 1]

-- Original cycle aaa3743d089effa09bce604e642d224263b3ecbdfaf76152daac273aad6eee1c; original global index 13296.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle ab4392981cfe4c228763b664cb831037e1ddd48d17b2ce5e1f45665e6ec62ff9; original global index 13344.
def localCycle00092 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 0 6, .distance 0 3]
    constant := ![-2, 2, 0, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 0 2, .gapUpper 5 4, .triangle 14 2, .gapLower 0 3]

-- Original cycle ab68a9bd7851493bdfe4a82b17c152e302d8bad42b1bdc5e9c5568abd530a24a; original global index 13355.
def localCycle00093 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ab7b57129e941ca9af6f0a24d38f4d7413948ca692ea6185311dfc66b802d1f6; original global index 13361.
def localCycle00094 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 0 3]
    constant := ![-2, -2, 2, 0, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.gapLower 0 2, .gapLower 0 1, .gapUpper 4 4, .triangle 32 2, .triangle 11 0]

-- Original cycle ad4d420998c459b5066614a3511f27c9c42ed83b4cd0262c898fb124d5329370; original global index 13509.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle af24a17ab563910b5ea1dbddecf8a04df1671a0547016e0efacf819ba29e540b; original global index 13679.
def localCycle00096 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 3, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .gapLower 3 0, .thetaLower 3]

-- Original cycle b283fb48a1682682643cc33722418a97b4ce2ca03ff51d1fe17ec337a7c15f56; original global index 13949.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b2df08b28a78e558ce2010441737acbb93288f2fe3c4f5b6a47c1dce1e5c2bda; original global index 13980.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 20 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b42aabc168cb8562e0db90f6526d45fe90973b3031813a05c165cff5a099633c; original global index 14070.
def localCycle00099 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -2, 3, 0, 0, -2, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3]

-- Original cycle b4f510713a4fb2eaec6b36066a4d4c74d82d8581170cd23b789337dfa307a2d6; original global index 14135.
def localCycle00100 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle bbad4a25dfd623b0f1a77633880b7dfea3638013c62e3d724018136cf533788a; original global index 14653.
def localCycle00101 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 4 4, .triangle 34 1, .triangle 14 0, .gapLower 0 1]

-- Original cycle bc6406c381b6b94594e1bb6f55aa0c7ea7e9587a78c3dc1bfe391598f4dfeea0; original global index 14700.
def localCycle00102 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .gapLower 5 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bd9d7a5afb06ab1ffd21dc9a53e6fb9ff345ec71f2daf6d4fe11a6ad4e09703c; original global index 14792.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 0 3, .distance 0 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 0 3, .triangle 10 2, .triangle 12 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle bff15a48449997d1b60b8fad3ae3731a75606e77d57ff181713813a347e6dd5f; original global index 14979.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle c0140fe255e0a7c22844f13bcd18b1965389af21c8ab242a257ab90dfdcaa34b; original global index 14993.
def localCycle00105 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 32 2, .gapUpper 3 6, .thetaLower 3]

-- Original cycle c0a8041c8a81353c631eb400bf2bcb0fd42248db9787cfc8b3bd1c3d5232948a; original global index 15045.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 32 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle c94dd3d37e3fc33a9acb62f638f548e91dde3417d1d02e43b6269319effe9636; original global index 15737.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle cdff42d6b8f1e11831218f294d1bda30af15c192105f248a862ca52f90d09403; original global index 16092.
def localCycle00108 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle d169e0df1ef737af2be2564c3d889a1e5cddaa38c847268d64d6f2ff65c94948; original global index 16347.
def localCycle00109 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .triangle 17 0, .triangle 28 1, .corridorLower 2 4]

-- Original cycle d4e9aefb6dd37eb63ad251edf64896f28dea25031c8a57107a511b9820b96775; original global index 16612.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d7e1a537b8b2d4e13fe01c576ea70f12caed1cdea3e103a589a07c0d9fa70503; original global index 16845.
def localCycle00111 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .theta 2, .theta 1]
    constant := ![3, -3, -2, 0]
    coefficient := ![1, 0, -1, 0]
    strict := ![false, false, true, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapUpper 2 6, .thetaNext 1]

-- Original cycle d8964c85a240dcb252ba945ede390c6b5337da43ab248cada6cfde8576a21f81; original global index 16904.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d962e6a62d748f5c037047e93eab34e1e14d37281711653c7866d029cefb8e25; original global index 16989.
def localCycle00113 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -2, 2, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3]

-- Original cycle dcf0e27fa17821652e3c3d75da30cdc434bc4da5ace0f5b20dc0b514648479b7; original global index 17269.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .gapLower 3 0, .thetaNext 2]

-- Original cycle dddbbee226a2c9774b04526606558885dfee43e2758a473806f62aead5f5aa33; original global index 17343.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle dde6bf47bd536ce992bb7d1d52f5b322f8ff0bf7a517a813641406d942c41964; original global index 17347.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle e13c9fc413cdeee2cc78ad64fd6187f4d821d88716fcecda794f85c9dc3245fe; original global index 17615.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .triangle 21 1, .triangle 19 0, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle e26b5f64dabb31c3e5eda86a88ac54f409b11d9806956dc437a01d4dae729853; original global index 17703.
def localCycle00118 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -2, 3, 0, -2, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 19 0, .corridorLower 1 3]

-- Original cycle e6a37ba36c66e7cdc1f250809f53fc859abb43244cec9c294cce712b9daccdad; original global index 18042.
def localCycle00119 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 25 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle e73f3187f857fe717836500e00d8396303c281b28c474adc9ce3b070bd5fd325; original global index 18089.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .triangle 21 1, .triangle 19 2, .triangle 22 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle ea8d3c41812a0222f3debc874b5755d224a996d8fe311587eb1d721dc36849eb; original global index 18321.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 27 1, .triangle 25 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle eb82349868e930169da4f545f9b88b22ddccb07c6c0348fe738a5e5c7230b920; original global index 18380.
def localCycle00122 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle ecf0169483f96e3e8042cb67b8fc1473ac4132208232d501405dceaaae309486; original global index 18494.
def localCycle00123 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1]

-- Original cycle ed30088d38f1fd9dbbbb2148d838d168c10c04c84661883426b70abe23523d04; original global index 18517.
def localCycle00124 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -3, 3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle ef43a1aa462d063ac4004117b18b9d887bc801cec61bfd1c52d5acddcb5357d9; original global index 18667.
def localCycle00125 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 31 1, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle efcc97dd7be79c8d8167f579823adb68e86dd920f31646391a897ac5ca1ec2b8; original global index 18711.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .triangle 21 1, .triangle 19 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle f31d6b6ec01bf02fcb096eba6996b64951fe3183cf9c2de16cdfb13b3e64d268; original global index 18952.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 11 0, .triangle 9 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .gapLower 3 0]

-- Original cycle f4e0b357c7c8c9f34c8fd012a2d21a0687508fd7eb61221f304d47fd64cb5cd1; original global index 19089.
def localCycle00128 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 2 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 11 2, .gapLower 6 2, .triangle 18 1, .gapLower 6 0]

-- Original cycle f5592c3f925d5e4eacf65d6c29d0e38ebc5d48fad20100400eedb770678943cb; original global index 19127.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle f59e28c86493d7923dad040ed68fd23ca285fa9f0b0df0a3478f9e83a051a922; original global index 19150.
def localCycle00130 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .theta 2, .theta 1]
    constant := ![3, -2, -2, 0]
    coefficient := ![1, 0, -1, 0]
    strict := ![false, false, true, true] }
  origin := ![.corridorUpper 0 1, .gapLower 0 5, .gapUpper 2 6, .thetaNext 1]

-- Original cycle f5ff7130ea2d7fffe010abe18925daffe47770f565e3e2b30e7101861bdccbec; original global index 19195.
def localCycle00131 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f84cd39f8066e0b56314b8ddcd10d66e58c4c373bde79f8914a2852805a2670f; original global index 19366.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 8 0, .triangle 18 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle f84d48b8e163bf85c033055c586bd325277132b764b5e204ede2a07b8d0074ea; original global index 19367.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 6, .distance 0 3, .distance 0 5, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .gapLower 0 4, .triangle 11 1, .gapLower 0 2, .gapLower 5 3, .triangle 17 0, .corridorLower 1 2]

-- Original cycle fa7933583ffdeb7aba2782381d9b01f111c739e88e44d7bd11751d82ae8bc839; original global index 19538.
def localCycle00134 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle fad905308f6c1f5add94ebeeb0ce2af7ea866c270c52af5eff8ff637ebc1561d; original global index 19573.
def localCycle00135 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle fd229cb510810a326bc0f8810d40c5312eb1c350f599f0f7218686a4c62a88e1; original global index 19781.
def localCycle00136 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 3, .distance 1 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 18 2, .triangle 21 1, .triangle 19 2, .triangle 22 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2, .thetaNext 1]

-- Original cycle fd9692715c79daa0d3a001737934992572353778f883fb1bc4fdd2844a8cd4ea; original global index 19823.
def localCycle00137 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle fe9e24decb34b0347465229d332637265df154a0c9c11d8efbd735b1b5d9b878; original global index 19905.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .triangle 15 1, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle fec8384289a91dd99642343f1cdff62aafdf939c140277bf522d0f666cd8e099; original global index 19922.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 11 0, .triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .corridorLower 3 5]

def library : Library := fun id => if id < 70 then (if id < 35 then (if id < 17 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))))) else (if id < 26 then (if id < 21 then (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))))) else (if id < 30 then (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))))))) else (if id < 52 then (if id < 43 then (if id < 39 then (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)))) else (if id < 47 then (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)))))) else (if id < 61 then (if id < 56 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))) else (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))))) else (if id < 65 then (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))))))) else (if id < 105 then (if id < 87 then (if id < 78 then (if id < 74 then (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))) else (if id < 82 then (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))))) else (if id < 96 then (if id < 91 then (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 93 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))))) else (if id < 100 then (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))))))) else (if id < 122 then (if id < 113 then (if id < 109 then (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))) else (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)))) else (if id < 117 then (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))) else (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))))) else (if id < 131 then (if id < 126 then (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))))) else (if id < 135 then (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))) else (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 5, 0, 6], ![3, 2, 1, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 100 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22784)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 1, 5, 2, 0, 6], ![3, 2, 1, 0, 5, 6], ![1, 3, 2, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 98 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22785)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 27 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22786)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 20 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22787)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 2, 1, 0, 5, 6], ![3, 1, 2, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 32 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22788)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 4, 5, 0, 6], ![2, 1, 3, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 129 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22789)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 27 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22790)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 5, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22791)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 38 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22792)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 5, 1, 0, 6], ![2, 3, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 16 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22793)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 49 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22794)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 5, 3, 1, 6, 0], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 79 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22795)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 5, 0, 6], ![1, 2, 3, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 125 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22796)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 0, 6], ![1, 3, 2, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 15 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22797)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 0, 6], ![1, 3, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 112 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22798)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 5, 0, 6], ![1, 2, 3, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 134 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22799)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 5, 0, 6], ![3, 1, 2, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 84 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22800)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 1, 5, 2, 0, 6], ![3, 1, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 62 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22801)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .low0 (![75, 85, 63, 0, 71, 111, 25, 101, 67, 103, 74, 130, 35, 94, 6, 77, 130, 101, 92, 133, 130, 67, 58, 130, 78, 130, 86, 130]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22802)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 4, 5, 0, 6], ![2, 1, 3, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 7 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22803)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 5, 0, 6], ![3, 2, 1, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 135 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22804)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 1, 5, 2, 0, 6], ![3, 2, 1, 0, 6, 5], ![1, 3, 2, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 98 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22805)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 60 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22806)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 6, 5], ![1, 2, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 87 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22807)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 2, 1, 0, 6, 5], ![3, 1, 2, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 34 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22808)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 4, 5, 0, 6], ![2, 1, 3, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 115 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22809)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 60 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22810)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 5, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 44 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22811)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 109 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22812)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 5, 1, 0, 6], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 16 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22813)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 49 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22814)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 5, 3, 1, 6, 0], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![1, 2, 0, 3, 5, 4]], proof := .tail 79 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22815)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 5, 0, 6], ![1, 2, 3, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 66 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22816)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 5, 4, 0, 6], ![1, 2, 5, 3, 0, 6], ![1, 2, 4, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 52 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22817)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 4, 0, 6], ![1, 5, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 42 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22818)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 4, 0, 6], ![1, 5, 2, 3, 0, 6], ![1, 4, 3, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 123 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22819)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 0, 6], ![1, 3, 2, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 69 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22820)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 0, 6], ![1, 3, 2, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 82 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22821)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 3, 6, 0], ![1, 4, 5, 2, 0, 6], ![1, 3, 5, 2, 0, 6], ![1, 3, 4, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 21 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22822)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 3, 6, 0], ![1, 5, 4, 2, 0, 6], ![1, 5, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 119 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22823)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 42 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22824)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 1, 3, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 76 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22825)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 3, 6, 0], ![1, 5, 4, 2, 0, 6], ![5, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 11 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22826)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![5, 1, 2, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 3, 1, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 56 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22827)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 4, 3, 6, 0], ![5, 1, 4, 2, 0, 6], ![5, 1, 3, 2, 0, 6], ![4, 3, 1, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 121 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22828)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![4, 1, 2, 5, 0, 6], ![3, 1, 2, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 82 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22829)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 1, 5, 2, 0, 6], ![3, 1, 2, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 62 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22830)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 4, 3, 5, 6, 0], ![1, 5, 4, 3, 6, 0], ![4, 1, 5, 2, 0, 6], ![3, 1, 5, 2, 0, 6], ![1, 3, 4, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 36 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22831)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 4, 5, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 1, 2, 5, 0, 6], ![3, 1, 2, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 82 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22832)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 4, 5, 3, 6, 0], ![1, 5, 4, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 1, 5, 2, 0, 6], ![3, 1, 4, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 28 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22833)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 5, 4, 3, 6, 0], ![1, 5, 4, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 5, 1, 2, 0, 6], ![3, 4, 1, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 10 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22834)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![2, 5, 4, 3, 6, 0], ![1, 5, 4, 3, 6, 0], ![5, 4, 1, 2, 0, 6], ![5, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22835)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 4, 6, 0], ![5, 1, 2, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 59 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22836)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 4, 3, 6, 0], ![5, 1, 4, 2, 0, 6], ![5, 1, 3, 2, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 14 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22837)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 2, 4, 3, 6, 0], ![5, 1, 4, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 5, 1, 2, 0, 6], ![3, 4, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 97 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22838)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 2, 4, 3, 6, 0], ![5, 1, 4, 3, 6, 0], ![5, 4, 1, 2, 0, 6], ![5, 3, 1, 2, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22839)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 3, 5, 6, 0], ![4, 1, 2, 5, 0, 6], ![3, 2, 1, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 57 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22840)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 2, 3, 5, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 1, 5, 2, 0, 6], ![3, 2, 1, 5, 0, 6], ![1, 3, 2, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 98 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22841)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 2, 5, 3, 6, 0], ![4, 1, 5, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 2, 1, 5, 0, 6], ![3, 1, 2, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 131 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22842)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 5, 2, 3, 6, 0], ![4, 5, 1, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 38 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22843)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 2, 3, 6, 0], ![4, 5, 1, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 90 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22844)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 2, 3, 6, 0], ![5, 4, 1, 3, 6, 0], ![4, 5, 1, 2, 0, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 114 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22845)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 2, 3, 6, 0], ![5, 4, 1, 3, 6, 0], ![5, 4, 1, 2, 0, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 18 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22846)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 4, 5, 0, 6], ![1, 2, 3, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 95 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22847)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 5, 4, 0, 6], ![1, 2, 5, 3, 0, 6], ![1, 2, 4, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22848)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 5, 4, 0, 6], ![1, 5, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 23 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22849)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 5, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 93 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22850)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 1, 5, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 2, 1, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 9 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22851)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 5, 1, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 2, 3, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 127 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22852)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 4, 6, 0], ![5, 2, 1, 4, 0, 6], ![5, 1, 2, 3, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 139 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22853)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 4, 5, 0, 6], ![2, 1, 3, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 104 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22854)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 5, 4, 0, 6], ![2, 1, 5, 3, 0, 6], ![1, 2, 4, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 102 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22855)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 64 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22856)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 3, 2, 5, 6, 0], ![4, 3, 1, 5, 6, 0], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 5, 0, 6], ![1, 2, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 137 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22857)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 4, 5, 0, 6], ![2, 1, 3, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 46 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22858)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 5, 4, 0, 6], ![2, 1, 5, 3, 0, 6], ![2, 1, 4, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 19 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22859)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 5, 4, 0, 6], ![2, 5, 1, 3, 0, 6], ![2, 4, 1, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 5 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22860)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 1, 5, 4, 0, 6], ![5, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 116 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22861)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 3, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 5, 1, 4, 0, 6], ![2, 5, 1, 3, 0, 6], ![2, 4, 3, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 127 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22862)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 3, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 5, 1, 4, 0, 6], ![5, 2, 1, 3, 0, 6], ![4, 2, 3, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 127 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22863)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 3, 4, 2, 6, 0], ![5, 3, 4, 1, 6, 0], ![5, 2, 1, 4, 0, 6], ![5, 2, 1, 3, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22864)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 3, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 64 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22865)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 3, 5, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22866)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 5, 3, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 5, 1, 0, 6], ![2, 3, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 16 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22867)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 49 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22868)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 5, 3, 2, 6, 0], ![4, 5, 3, 1, 6, 0], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 79 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22869)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 4, 5, 1, 0, 6], ![2, 3, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 39 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22870)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 5, 4, 1, 0, 6], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 48 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22871)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 5, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 132 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22872)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 2, 6, 0], ![5, 3, 4, 1, 6, 0], ![5, 2, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 43 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22873)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 2, 6, 0], ![4, 3, 5, 1, 6, 0], ![4, 2, 5, 1, 0, 6], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 53 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22874)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 2, 6, 0], ![4, 5, 3, 1, 6, 0], ![4, 5, 2, 1, 0, 6], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 45 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22875)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 2, 6, 0], ![5, 4, 3, 1, 6, 0], ![4, 5, 2, 1, 0, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 110 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22876)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 2, 6, 0], ![5, 4, 3, 1, 6, 0], ![5, 4, 2, 1, 0, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![1, 2, 0, 3, 4, 5]], proof := .tail 65 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22877)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 5, 0, 6], ![2, 1, 3, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .low6 (![124, 40, 26, 83, 96, 30, 80, 8, 128, 99, 118, 22, 113, 73, 61, 122, 72, 1, 89, 122, 72, 29, 4, 106, 91, 12, 51, 105]) }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22878)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 27 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22879)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 5, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 1, 3, 0, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 17 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22880)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 1, 0, 6], ![2, 3, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 55 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22881)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![2, 3, 1, 0, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 68 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22882)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 5, 6], ![3, 2, 1, 0, 4, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 108 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22883)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 5, 0, 6], ![2, 1, 3, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .tail 70 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22884)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .tail 60 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22885)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 3, 5, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 1, 3, 0, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .tail 138 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22886)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 1, 0, 6], ![2, 3, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .tail 55 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22887)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![2, 3, 1, 0, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .tail 68 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22888)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![4, 5, 3, 6, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 0, 6, 5], ![3, 2, 1, 0, 6, 4], ![2, 1, 0, 3, 5, 4]], proof := .tail 108 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22889)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 4, 5, 0, 6], ![2, 1, 3, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 46 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22890)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 5, 4, 0, 6], ![2, 1, 5, 3, 0, 6], ![2, 1, 4, 3, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 19 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22891)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 5, 4, 0, 6], ![2, 5, 1, 3, 0, 6], ![2, 4, 1, 3, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 54 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22892)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 5, 4, 0, 6], ![5, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 47 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22893)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 3, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 5, 1, 4, 0, 6], ![2, 5, 1, 3, 0, 6], ![2, 4, 3, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 127 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22894)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 3, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 1, 4, 0, 6], ![5, 2, 1, 3, 0, 6], ![4, 2, 3, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 127 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22895)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 3, 4, 6, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 1, 4, 0, 6], ![5, 2, 1, 3, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 56 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22896)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 3, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 1, 5, 0, 6], ![2, 3, 1, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 64 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22897)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 3, 5, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 1, 5, 0, 6], ![3, 2, 1, 5, 0, 6], ![2, 1, 3, 4, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 107 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22898)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 5, 3, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 1, 0, 6], ![2, 3, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 88 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22899)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 1, 0, 6], ![3, 2, 1, 5, 0, 6], ![2, 3, 1, 4, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 68 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22900)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![4, 5, 3, 6, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 1, 0, 6], ![3, 2, 1, 5, 0, 6], ![3, 2, 1, 4, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 108 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22901)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 4, 5, 1, 0, 6], ![2, 3, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 33 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22902)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 5, 4, 1, 0, 6], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 126 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22903)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 117 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22904)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 6, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 4, 1, 0, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 24 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22905)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 6, 2, 0], ![4, 3, 5, 6, 1, 0], ![4, 2, 5, 1, 0, 6], ![3, 2, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 136 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22906)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 6, 2, 0], ![4, 5, 3, 6, 1, 0], ![4, 5, 2, 1, 0, 6], ![3, 2, 5, 1, 0, 6], ![3, 2, 4, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 120 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22907)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 6, 2, 0], ![5, 4, 3, 6, 1, 0], ![4, 5, 2, 1, 0, 6], ![3, 5, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 2 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22908)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![5, 4, 3, 6, 2, 1], ![5, 4, 3, 6, 2, 0], ![5, 4, 3, 6, 1, 0], ![5, 4, 2, 1, 0, 6], ![5, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 1, 0, 3, 4, 5]], proof := .tail 50 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22909)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 4, 5, 6, 0], ![1, 2, 3, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 3 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22910)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![4, 5, 6, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 6, 0], ![1, 3, 2, 0, 5, 6], ![1, 2, 3, 0, 4, 6], ![1, 2, 3, 0, 4, 5]], proof := .tail 13 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22911)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then
  (if offset < 32 then
  (if offset < 16 then
  (if offset < 8 then
  (if offset < 4 then
  (if offset < 2 then
  (if offset < 1 then
  (namedLeaf000) else
  (namedLeaf001)) else
  (if offset < 3 then
  (namedLeaf002) else
  (namedLeaf003))) else
  (if offset < 6 then
  (if offset < 5 then
  (namedLeaf004) else
  (namedLeaf005)) else
  (if offset < 7 then
  (namedLeaf006) else
  (namedLeaf007)))) else
  (if offset < 12 then
  (if offset < 10 then
  (if offset < 9 then
  (namedLeaf008) else
  (namedLeaf009)) else
  (if offset < 11 then
  (namedLeaf010) else
  (namedLeaf011))) else
  (if offset < 14 then
  (if offset < 13 then
  (namedLeaf012) else
  (namedLeaf013)) else
  (if offset < 15 then
  (namedLeaf014) else
  (namedLeaf015))))) else
  (if offset < 24 then
  (if offset < 20 then
  (if offset < 18 then
  (if offset < 17 then
  (namedLeaf016) else
  (namedLeaf017)) else
  (if offset < 19 then
  (namedLeaf018) else
  (namedLeaf019))) else
  (if offset < 22 then
  (if offset < 21 then
  (namedLeaf020) else
  (namedLeaf021)) else
  (if offset < 23 then
  (namedLeaf022) else
  (namedLeaf023)))) else
  (if offset < 28 then
  (if offset < 26 then
  (if offset < 25 then
  (namedLeaf024) else
  (namedLeaf025)) else
  (if offset < 27 then
  (namedLeaf026) else
  (namedLeaf027))) else
  (if offset < 30 then
  (if offset < 29 then
  (namedLeaf028) else
  (namedLeaf029)) else
  (if offset < 31 then
  (namedLeaf030) else
  (namedLeaf031)))))) else
  (if offset < 48 then
  (if offset < 40 then
  (if offset < 36 then
  (if offset < 34 then
  (if offset < 33 then
  (namedLeaf032) else
  (namedLeaf033)) else
  (if offset < 35 then
  (namedLeaf034) else
  (namedLeaf035))) else
  (if offset < 38 then
  (if offset < 37 then
  (namedLeaf036) else
  (namedLeaf037)) else
  (if offset < 39 then
  (namedLeaf038) else
  (namedLeaf039)))) else
  (if offset < 44 then
  (if offset < 42 then
  (if offset < 41 then
  (namedLeaf040) else
  (namedLeaf041)) else
  (if offset < 43 then
  (namedLeaf042) else
  (namedLeaf043))) else
  (if offset < 46 then
  (if offset < 45 then
  (namedLeaf044) else
  (namedLeaf045)) else
  (if offset < 47 then
  (namedLeaf046) else
  (namedLeaf047))))) else
  (if offset < 56 then
  (if offset < 52 then
  (if offset < 50 then
  (if offset < 49 then
  (namedLeaf048) else
  (namedLeaf049)) else
  (if offset < 51 then
  (namedLeaf050) else
  (namedLeaf051))) else
  (if offset < 54 then
  (if offset < 53 then
  (namedLeaf052) else
  (namedLeaf053)) else
  (if offset < 55 then
  (namedLeaf054) else
  (namedLeaf055)))) else
  (if offset < 60 then
  (if offset < 58 then
  (if offset < 57 then
  (namedLeaf056) else
  (namedLeaf057)) else
  (if offset < 59 then
  (namedLeaf058) else
  (namedLeaf059))) else
  (if offset < 62 then
  (if offset < 61 then
  (namedLeaf060) else
  (namedLeaf061)) else
  (if offset < 63 then
  (namedLeaf062) else
  (namedLeaf063))))))) else
  (if offset < 96 then
  (if offset < 80 then
  (if offset < 72 then
  (if offset < 68 then
  (if offset < 66 then
  (if offset < 65 then
  (namedLeaf064) else
  (namedLeaf065)) else
  (if offset < 67 then
  (namedLeaf066) else
  (namedLeaf067))) else
  (if offset < 70 then
  (if offset < 69 then
  (namedLeaf068) else
  (namedLeaf069)) else
  (if offset < 71 then
  (namedLeaf070) else
  (namedLeaf071)))) else
  (if offset < 76 then
  (if offset < 74 then
  (if offset < 73 then
  (namedLeaf072) else
  (namedLeaf073)) else
  (if offset < 75 then
  (namedLeaf074) else
  (namedLeaf075))) else
  (if offset < 78 then
  (if offset < 77 then
  (namedLeaf076) else
  (namedLeaf077)) else
  (if offset < 79 then
  (namedLeaf078) else
  (namedLeaf079))))) else
  (if offset < 88 then
  (if offset < 84 then
  (if offset < 82 then
  (if offset < 81 then
  (namedLeaf080) else
  (namedLeaf081)) else
  (if offset < 83 then
  (namedLeaf082) else
  (namedLeaf083))) else
  (if offset < 86 then
  (if offset < 85 then
  (namedLeaf084) else
  (namedLeaf085)) else
  (if offset < 87 then
  (namedLeaf086) else
  (namedLeaf087)))) else
  (if offset < 92 then
  (if offset < 90 then
  (if offset < 89 then
  (namedLeaf088) else
  (namedLeaf089)) else
  (if offset < 91 then
  (namedLeaf090) else
  (namedLeaf091))) else
  (if offset < 94 then
  (if offset < 93 then
  (namedLeaf092) else
  (namedLeaf093)) else
  (if offset < 95 then
  (namedLeaf094) else
  (namedLeaf095)))))) else
  (if offset < 112 then
  (if offset < 104 then
  (if offset < 100 then
  (if offset < 98 then
  (if offset < 97 then
  (namedLeaf096) else
  (namedLeaf097)) else
  (if offset < 99 then
  (namedLeaf098) else
  (namedLeaf099))) else
  (if offset < 102 then
  (if offset < 101 then
  (namedLeaf100) else
  (namedLeaf101)) else
  (if offset < 103 then
  (namedLeaf102) else
  (namedLeaf103)))) else
  (if offset < 108 then
  (if offset < 106 then
  (if offset < 105 then
  (namedLeaf104) else
  (namedLeaf105)) else
  (if offset < 107 then
  (namedLeaf106) else
  (namedLeaf107))) else
  (if offset < 110 then
  (if offset < 109 then
  (namedLeaf108) else
  (namedLeaf109)) else
  (if offset < 111 then
  (namedLeaf110) else
  (namedLeaf111))))) else
  (if offset < 120 then
  (if offset < 116 then
  (if offset < 114 then
  (if offset < 113 then
  (namedLeaf112) else
  (namedLeaf113)) else
  (if offset < 115 then
  (namedLeaf114) else
  (namedLeaf115))) else
  (if offset < 118 then
  (if offset < 117 then
  (namedLeaf116) else
  (namedLeaf117)) else
  (if offset < 119 then
  (namedLeaf118) else
  (namedLeaf119)))) else
  (if offset < 124 then
  (if offset < 122 then
  (if offset < 121 then
  (namedLeaf120) else
  (namedLeaf121)) else
  (if offset < 123 then
  (namedLeaf122) else
  (namedLeaf123))) else
  (if offset < 126 then
  (if offset < 125 then
  (namedLeaf124) else
  (namedLeaf125)) else
  (if offset < 127 then
  (namedLeaf126) else
  (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (22784 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 22784 ≤ id.val) (hhigh : id.val < 22912) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 22784)) = true := by
  let j : Fin 128 := ⟨id.val - 22784, by omega⟩
  have hsum : 22784 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (22784 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard178
