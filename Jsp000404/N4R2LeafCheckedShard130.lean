import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard130
open N4R2RowDataReplay

-- Original cycle 01d14fbbea6d22cd7d4e9394b802e0065f2d9dee2d48bd042482b05da229de8f; original global index 146.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .gapLower 2 4, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 0f1a4232e053f8e3d3dc057cbe285434ec243304aa975af3f82d99ff62179063; original global index 1201.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 21 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 103a187149543fd1cf8d21b71b472498c6ef191e82c6e9c7b3d01bdd2f40c9fa; original global index 1304.
def localCycle00002 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 16da49ac06eb972bce512e975510b7bb40c8cd3a39bbb0bb9fb18c7768c29775; original global index 1799.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 1bc26e8c986b59c5d9a3c364c6347fcc795eea2679128aeff8e9c3a217f5e370; original global index 2146.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 18 0, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 21116c16ee23f052314aa309c2a1eace42518073e170f17a7e4a3628833ceb7b; original global index 2536.
def localCycle00005 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true] }
  origin := ![.triangle 0 0, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle 2551b5ec6abe676ac1080a8a69d9f0563b1ccddbda86a8c091e82a917a9e39d7; original global index 2869.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 26e9815e083d233f8f3b4ed40d0982e582b7da5b7d8ea11f57e14f3893ea4ce9; original global index 2981.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 27e1b736a12e53a917e674d2c323d381ba621140ee96b77837094a03de9be5c5; original global index 3051.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 23 0, .corridorLower 4 6]

-- Original cycle 2bdf4e600f9918347f4729f0c7f5839a4d14537bbb50f9eadc1e8eab3b80eb62; original global index 3357.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2d009fdd60bfdfe75cb278fe60304d851e154bf77ff6099fae2292e7180b4ddf; original global index 3438.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 32f516069c9f2686d8b10730337c57c9f986c3b29ac711d3bd1ed78a125db6b7; original global index 3904.
def localCycle00011 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 0 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle 3345d129b845160f13cb7429103c19ba6c83920723a61fde789fd32aea2cc099; original global index 3923.
def localCycle00012 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 3a3a9c60e939b9a49959e1b9a5a969d2f51de25bdb986f151b565cb743c98120; original global index 4498.
def localCycle00013 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 3bd648812ca069cdb976e0e5b78d51c9c67efb68422de638ef7c88d0461e3819; original global index 4632.
def localCycle00014 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .gapUpper 5 1, .triangle 10 1]

-- Original cycle 3c83e503b587804e8fa6245de1215d64d12470413e6799980a0a204f335a3dfe; original global index 4695.
def localCycle00015 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle 42d64b38108c32d7074aa7e8893b7164e38f71925e454a52a1569220382c16cc; original global index 5144.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 18 0, .triangle 30 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 44b68075261c529e17bf2307384cf26c2eabfa9aee7a52c7deb8333c17053063; original global index 5326.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 47ec77b62bff821a9ef94a4c36f8e04354e3718763ab66e651db432b37bed29c; original global index 5567.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4967b209ab89732a4122db95a6362eb2c4ee4158fb3c560177ee4001774f158e; original global index 5687.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4a3edf1067de5b4c78a2779be360577702a0a3a73b9c109d341ff437ecead84e; original global index 5759.
def localCycle00020 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4c4ca01d953df27b87c1ffcfc4f832ac775f8857b65cc70e8561dd27040017b1; original global index 5923.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true] }
  origin := ![.triangle 5 0, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 4d4bffc4fa8cfbf325e349c01cdb2ff7db28dc69d592e553377be2a512854c06; original global index 6003.
def localCycle00022 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 50711a628f7cb3e543c117441d1216d4249f77dbf912db667ddfdbfe7ff03f30; original global index 6246.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 55944a01859ee766a2c071fa5c065928c10d46b7d5e3851efa565e50f4a215a5; original global index 6632.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 55e38093fd517d5b9e5a17beb356b9e03584eaca5b88bd33fcce5b446505fd1f; original global index 6658.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 575358f6b47e070fe1a3aa7dfbe8873e419617607fe5f0617dac7b3398fddb86; original global index 6768.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 5756114120e9eb9a689077d0e682fb4848e9b5f0184a498f0f6a7a70c4c3868a; original global index 6770.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5be576cd7c3975c6990818fd1acaeebb3bf2148f1de6c94ddfb887615c49bb9b; original global index 7145.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 5c9a4a33bfdacee4b57215fbf08d3ddd2bfe4c29383b66d44534c474c8c18af6; original global index 7206.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 6111a8b1119171d95f694641bec2ff9005af4edfc13111d1552f41ba6df56aa4; original global index 7572.
def localCycle00030 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 62096406c3cf32f97496ae2459c37ae2334bea721a6aee1baad49e8f121db055; original global index 7655.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6446a22b3b60f2f3caf5e4be23c0e757a843bf238b3292d2df2424739ca7bc7a; original global index 7812.
def localCycle00032 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 0 0, .triangle 15 0, .triangle 27 0, .triangle 33 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle 66463ca02a53ce3f2f2e7839397ed2bb63ab7fe523a6b2c286638ba8408b2d0d; original global index 7955.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, 0, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, true] }
  origin := ![.triangle 9 0, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .gapUpper 5 1, .triangle 10 1]

-- Original cycle 67ebda1fee897c157af3465db76260c619900ddbc503bf7f006d60a1a6331258; original global index 8078.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 23 0, .gapLower 1 1, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 6b6461a4c74e6eced678dc5859de01b7b5ed75ba036a13e6cb041da1316c4ca3; original global index 8359.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 6c9a38845ce2ab387f32048139c53f493267d033fe9708905a9db57da5559bbe; original global index 8448.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, true] }
  origin := ![.triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .triangle 33 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 6cab4271345dfdaaa9e9d3c3c2264867dcf2ff8e3c4794bf70654e67b204442d; original global index 8454.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 706af6ee31d4a5b0b1e4bd6daca5bcd61616b6d71b465077ad00bc6150e6fe8c; original global index 8709.
def localCycle00038 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 75fb5127ce16540352c9fb797a87d889447139a3ded3321bdc6371c90e4b2996; original global index 9140.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 10 1]

-- Original cycle 768dc1c213bba391f8d743c5e4b9fd86aad80e446df86adbd6ca5681a6bb90d6; original global index 9175.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, 0, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true] }
  origin := ![.triangle 0 0, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle 773b52a004665a62f3aec9973079ce9806eb247cc9b1d432379001a4e7fac89c; original global index 9228.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true] }
  origin := ![.triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 7d3e8d557ee358913954fb1760259c2c2c70685d2dcfefa7ceba7a06f5ea1ce1; original global index 9707.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 24 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 7d9b8e09d6f9224df6871b0d0a6fcf7184cc7bcd64204109289f2e9b87da2baa; original global index 9749.
def localCycle00043 : Cycle where
  length := 13
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, 0, 0, -1, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 15 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 7dfbba5e73f0f9083cbc0b2f595c57530c2052231335e16259203e838e83a2ac; original global index 9784.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 7f8fb7e1ffc44c04a708746f0ede5791719b55127c4db01b01afe80d5a23abb5; original global index 9894.
def localCycle00045 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 81e24af9d43a691c2765a3a47f12d7b9cee3ea15166f9074e5b71d42e61c9306; original global index 10084.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 88ad4493de4e88ca82e6869ae00b4a12200b1357a969edef42a57f1053a239d2; original global index 10589.
def localCycle00047 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 8be6b271c0b1cace0e77b9b38b7836304f2865cc13bba215551d3ef3a157f45d; original global index 10829.
def localCycle00048 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 2, .triangle 8 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8cad17885010e0f5e2be494ff6cb09b8de89d4a17fbdbab4c54e43b2d0952077; original global index 10881.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8d0f0c2c73c394b8712f6005b2b2359369591d3710f9fc5edbff0a228341db79; original global index 10911.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, 0, -1, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .gapLower 5 3, .triangle 3 0, .triangle 0 2, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 8e01ea99e8b59959ccb5966398f477e98a3a1f27313e5168d1c403fed706ef9c; original global index 10997.
def localCycle00051 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8ffb17d66bb5439fe7d40a80335edbb28ddebdaae19415a4b64214c1ba71d45b; original global index 11146.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 8 0, .triangle 18 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 90e4fe12cc124407375a98960d8502727d10a4832f1ddc5443e7705825083c68; original global index 11219.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 2, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 18 1, .triangle 16 0, .gapLower 4 0]

-- Original cycle 93bc634f8a8ea3b24bfc71bef015b7d110d96686d264322ecd9651a13891ccb1; original global index 11463.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .gapUpper 5 1, .triangle 10 1]

-- Original cycle 94bde2ea139b323a43c305bbfa224617bf00ecf2d3cec489681e53fd3e5f1315; original global index 11543.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 9806a2c9b1be75e63b161cd99e46d46760a1ad3ed231b41b6a4084b237c03130; original global index 11809.
def localCycle00056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 5 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 9a3e59982dad6982d1d1165eb16eb40d6c0f0868dccdf64456202dc822e236bb; original global index 11985.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 9c3489fd8db55eeaafc228628913fc842887c767c907bc7ce27ac8bafaa6e8f9; original global index 12152.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 9cc32d79d974c76fbfa3914ef529e3218975fab7a0b8a55f321f7379bd8161ac; original global index 12193.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 9ccd4f356adf7014bf347822d01b788f9919ab228cdd33273fcee52984727689; original global index 12196.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle 9e47e8de0462055b776a50151b02d1ea8d3004d88114c55ccbb371a0e1a8894c; original global index 12320.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 9fadbff9d08bedfaa09f8c94b2fbe63ce5436a3b93e2577676528404d4852c12; original global index 12427.
def localCycle00062 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 0, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 25 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a0636e7241edc0e7f1a150ad9b8c17d31cdbd0c8516ae966708b40102e87b2bc; original global index 12482.
def localCycle00063 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 33 1, .corridorLower 5 6]

-- Original cycle a68f2a8ec7cbee0d4bf8d25e32b6f5d130830522b9be1e16f65f830924c1831a; original global index 12938.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true, true] }
  origin := ![.triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle a71df72dba941731644beac9beb91be2d6f1d2500ecc44a90c7385bcaa2467b1; original global index 12991.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, 0, -1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true] }
  origin := ![.triangle 0 0, .triangle 15 2, .triangle 19 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle a94fc37ae3539e13161d6931cb0b59fd5c9a435bf3340715e5c609b5cc104950; original global index 13184.
def localCycle00066 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 4, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 0, .triangle 19 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle aa95dc07d3bce474b88c36bd5fc250189bf3ec3d27ebe6564f5e32085726aec7; original global index 13290.
def localCycle00067 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b03d9b358ba261450161128af0ba14d81262cac98e0aebac00fed2f07b954126; original global index 13759.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b1b4572e8ed614e1df052850cc900721fdf81ca5b1cc5881b16df0713358ed21; original global index 13886.
def localCycle00069 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b54f7167de24137e001e7c3f7fc19fbccca477025f3a966b9aec786b9fa9b1b2; original global index 14165.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b5d77e85198417730378359ff7daa3bc655e189209b85e4b76990d88f1cac5d1; original global index 14208.
def localCycle00071 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, 0, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true] }
  origin := ![.triangle 5 0, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle b652f228fb334b237adf446f8b9a92e0255a39e7fed7bb319273fcbe1d8eb101; original global index 14248.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle b672c0b77ef9a9616f933f124329fc02805935dcfdbeb3ee48329d1d98234a5d; original global index 14260.
def localCycle00073 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b7cc7945f5232ab33e2171c727078092a345bbf2a82693b9f7956d5abcc301ca; original global index 14342.
def localCycle00074 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, 0, -1, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 6, .gapLower 5 3, .triangle 3 0, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle ba5fd147025c23961cfb86877f6a745225a9e2f220e3d315ec7dda4b25e622b4; original global index 14554.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 0, .triangle 19 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle bf1a8c8674cba165fbdcdfd440e547943cd13a752d680cf93b3d5881c230397f; original global index 14910.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c226c7f85ab37c3d5ab45a0a8a77ea47537e6f74b5725333e1466ee24870d2af; original global index 15159.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cbd9d683d0896b68dc35d3ec2e26c72aa04a5147190beaffa3b315c9983308ff; original global index 15930.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle ce5d4f46d8551b8c881ef28b97aa8946b6521ec6e432b5efd7ade475b395adc3; original global index 16122.
def localCycle00079 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 23 0, .gapLower 4 0]

-- Original cycle ce884f9e7e891830b6003c539e8470f37d13ae3dddb8f5150911db13665354cb; original global index 16129.
def localCycle00080 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle cf549eeabba4580072cd89168de67b3224c54e20244d0674f0d5b1a602098bb9; original global index 16182.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d01e067f9cdb15d33ea617741fd303342c35da473c0d328e5bcf46769855a9d5; original global index 16246.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 21 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle d0b94bd5aea0071f1c43401ed459b97a6b5faa11d6c11e1a6ef38cc04207cfd7; original global index 16289.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle d10b2524c224326949baa02f1ec7d930ebc21d7d470a3f72edcdad2899c6bb01; original global index 16322.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d2a0a4682a695c0b42a896cf48b024ab81ef19ab05c2de20ee1be4a592835445; original global index 16437.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d384ad952472d462e0f3c082844011fd310ec943f9737419aa77b5c95fe62556; original global index 16505.
def localCycle00086 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle d7fe2389d6a1108a966ea68d929d0a5f18c8b927bb797ecb6e1dcdc5097eac0b; original global index 16857.
def localCycle00087 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 9 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle d98630b5ace6de81b02708aaa6cbea6de3b40e922df7927a2fdeb754f5741f57; original global index 16997.
def localCycle00088 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 17 2, .triangle 3 0, .triangle 4 0, .triangle 23 1, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle dacfd030a272c8f9426a8526080c5f723fc9cd31fb87b03a106e1e939b85f71b; original global index 17100.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 29 0, .corridorLower 4 6]

-- Original cycle db3ca99c5a09601cabe6666ae8bc630e93dace9fbe3d124b85ff1e6e3d3600e2; original global index 17136.
def localCycle00090 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e1d8adb39831753695b410b1dff17d7dc7e7a34f9f82ccf127483ff068bef45f; original global index 17661.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, -1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.triangle 0 0, .triangle 15 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle e52aca45c329a10430bcd37caa8bc2745bac7dc6f63a7da431e2a6807211677c; original global index 17914.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 19 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle e6d3753f8ca03c66924d3701aca14227c5b7199dd5715341eb97afda34083180; original global index 18060.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .gapLower 5 4, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e85b777bbb3e8ffc66c62febf45700cccf0a20fca574fb3444f1f4e815bed941; original global index 18164.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 1]
    constant := ![-1, 0, -1, 0, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true] }
  origin := ![.triangle 0 0, .triangle 15 2, .triangle 19 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .gapUpper 5 1, .triangle 3 1]

-- Original cycle e8d73106310bba4bb05a378b1f9033dd4a3fb56ffb9b7822ad80a72f4042abb9; original global index 18199.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle ec3be20b85f7995543d79cb038d2538ae5e43c745e91ba404a36689224a4197f; original global index 18438.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle eca831ab09ad77e75139680bfce7a3ddb99e6213c831175768a1a7a16ac389c9; original global index 18477.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 19 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .corridorLower 5 6]

-- Original cycle f177f3b99c3a091e61076e15c3b90fa241e690bd796aae46cb8feeb7e7d02ce6; original global index 18828.
def localCycle00098 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 10 0, .triangle 9 0, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f9ce3700364b5cf5178a106966c67504da0cab20281bd0d456cae7a4ab974beb; original global index 19480.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 3]
    constant := ![-1, -1, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .gapUpper 5 1, .triangle 10 1]

-- Original cycle fb84d3ae79ef15551af9e6bae58bf51aa4e27dd0805bf34fa1853155e6a288ad; original global index 19638.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 21 0, .gapLower 1 2, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle fc59c191002f9534bd56eb36b1e90f6ad9e98c31c35001d8c7da4f0481e02f4b; original global index 19711.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 15 2, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

def library : Library := fun id => if id < 51 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 38 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))))) else (if id < 44 then (if id < 41 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)))) else (if id < 47 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))))))) else (if id < 76 then (if id < 63 then (if id < 57 then (if id < 54 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)))) else (if id < 60 then (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))))) else (if id < 69 then (if id < 66 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))) else (if id < 72 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))) else (if id < 74 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))))) else (if id < 89 then (if id < 82 then (if id < 79 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))) else (if id < 85 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))) else (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none))))) else (if id < 95 then (if id < 92 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)))) else (if id < 98 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 12 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16640)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 3 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16641)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 0, 4]], proof := .tail 100 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16642)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 3, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 4, 1, 6, 0, 5], ![2, 3, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 50 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16643)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 3, 2, 6, 0, 5], ![4, 3, 1, 6, 0, 5], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 0, 4]], proof := .tail 28 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16644)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 2, 6, 3, 0, 5], ![4, 1, 6, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 2, 0, 4]], proof := .tail 25 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16645)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![3, 4, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 4 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16646)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 3, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 4, 1, 6, 0, 5], ![2, 3, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 92 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16647)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 3, 6, 2, 0, 5], ![4, 3, 6, 1, 0, 5], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 3, 0, 4]], proof := .tail 18 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16648)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 6, 2, 3, 0, 5], ![4, 6, 1, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 29 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16649)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 6, 3, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 4, 6, 1, 0, 5], ![2, 3, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 15 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16650)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 6, 3, 2, 0, 5], ![4, 3, 6, 1, 0, 5], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 22 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16651)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![4, 6, 3, 2, 1, 5], ![4, 6, 3, 2, 0, 5], ![4, 6, 3, 1, 0, 5], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 32 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16652)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 6, 0, 5], ![1, 2, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 10 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16653)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 37 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16654)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 46 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16655)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 39 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16656)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 3, 6, 0, 5], ![1, 4, 2, 6, 0, 5], ![1, 3, 2, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 27 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16657)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 4, 6, 3, 0, 5], ![1, 4, 6, 2, 0, 5], ![1, 3, 2, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 31 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16658)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 4, 3, 0, 5], ![1, 4, 6, 2, 0, 5], ![1, 3, 6, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 73 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16659)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 4, 3, 0, 5], ![1, 6, 4, 2, 0, 5], ![1, 6, 3, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 56 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16660)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 75 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16661)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 39 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16662)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 4, 3, 0, 5], ![1, 6, 4, 2, 0, 5], ![6, 1, 3, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 56 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16663)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 3, 4, 0, 5], ![6, 1, 2, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 99 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16664)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 4, 3, 0, 5], ![6, 1, 4, 2, 0, 5], ![6, 1, 3, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16665)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 1, 2, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 69 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16666)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 4, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 1, 2, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 82 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16667)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 4, 3, 6, 0, 5], ![1, 6, 4, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 1, 6, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 4, 2, 0]], proof := .tail 78 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16668)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 4, 6, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 1, 2, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 31 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16669)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 4, 6, 3, 0, 5], ![1, 6, 4, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 1, 6, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 6 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16670)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 6, 4, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 6, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 63 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16671)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![2, 6, 4, 3, 0, 5], ![1, 6, 4, 3, 0, 5], ![6, 4, 1, 2, 0, 5], ![6, 3, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 21 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16672)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 3, 4, 0, 5], ![6, 1, 2, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 30 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16673)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 4, 3, 0, 5], ![6, 1, 4, 2, 0, 5], ![6, 1, 3, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 26 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16674)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 2, 4, 3, 0, 5], ![6, 1, 4, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 6, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 36 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16675)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 2, 4, 3, 0, 5], ![6, 1, 4, 3, 0, 5], ![6, 4, 1, 2, 0, 5], ![6, 3, 1, 2, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 64 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16676)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 3, 6, 0, 5], ![4, 1, 2, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 2 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16677)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 2, 3, 6, 0, 5], ![4, 1, 6, 3, 0, 5], ![4, 1, 6, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 3, 2, 4, 0]], proof := .tail 100 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16678)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 2, 6, 3, 0, 5], ![4, 1, 6, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 2, 4, 0]], proof := .tail 25 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16679)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 6, 2, 3, 0, 5], ![4, 6, 1, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 29 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16680)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 2, 3, 0, 5], ![4, 6, 1, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 71 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16681)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 2, 3, 0, 5], ![6, 4, 1, 3, 0, 5], ![4, 6, 1, 2, 0, 5], ![3, 6, 2, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 41 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16682)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 2, 3, 0, 5], ![6, 4, 1, 3, 0, 5], ![6, 4, 1, 2, 0, 5], ![6, 3, 2, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 57 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16683)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![1, 2, 3, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 19 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16684)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 6, 0, 5], ![2, 1, 6, 4, 0, 5], ![1, 2, 6, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 38 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16685)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 4, 0, 5], ![1, 6, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 67 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16686)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 2, 6, 4, 0, 5], ![3, 1, 6, 4, 0, 5], ![2, 1, 6, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 47 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16687)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 6, 2, 4, 0, 5], ![3, 6, 1, 4, 0, 5], ![2, 1, 6, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 33 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16688)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 3, 2, 4, 0, 5], ![3, 6, 1, 4, 0, 5], ![2, 6, 1, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 14 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16689)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 3, 2, 4, 0, 5], ![6, 3, 1, 4, 0, 5], ![6, 2, 1, 4, 0, 5], ![6, 1, 2, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 59 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16690)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 66 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16691)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 1, 6, 4, 0, 5], ![2, 1, 6, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 98 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16692)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 3, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 4, 1, 6, 0, 5], ![2, 3, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 74 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16693)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 3, 2, 6, 0, 5], ![4, 3, 1, 6, 0, 5], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 1, 2, 3, 4, 0]], proof := .tail 43 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16694)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 4, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 4, 6, 0, 5], ![2, 1, 3, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 61 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16695)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 4, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 4, 0, 5], ![2, 1, 6, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 34 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16696)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 6, 4, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 6, 4, 0, 5], ![2, 6, 1, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 97 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16697)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![3, 6, 4, 2, 0, 5], ![3, 6, 4, 1, 0, 5], ![2, 1, 6, 4, 0, 5], ![6, 2, 1, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 11 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16698)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 3, 4, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 6, 1, 4, 0, 5], ![2, 6, 1, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 54 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16699)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 3, 4, 2, 0, 5], ![3, 6, 4, 1, 0, 5], ![2, 6, 1, 4, 0, 5], ![6, 2, 1, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 14 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16700)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 3, 4, 2, 0, 5], ![6, 3, 4, 1, 0, 5], ![6, 2, 1, 4, 0, 5], ![6, 2, 1, 3, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 99 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16701)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 3, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 4, 1, 6, 0, 5], ![2, 3, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 83 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16702)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 3, 6, 2, 0, 5], ![4, 3, 6, 1, 0, 5], ![4, 2, 1, 6, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 1, 3, 4, 0]], proof := .tail 87 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16703)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 6, 3, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 4, 6, 1, 0, 5], ![2, 3, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 15 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16704)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 6, 3, 2, 0, 5], ![4, 3, 6, 1, 0, 5], ![4, 2, 6, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 22 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16705)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![4, 6, 3, 2, 0, 5], ![4, 6, 3, 1, 0, 5], ![4, 6, 2, 1, 0, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 32 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16706)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 3, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 4, 6, 1, 0, 5], ![2, 3, 6, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 62 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16707)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 3, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 6, 4, 1, 0, 5], ![2, 6, 3, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 40 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16708)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 3, 2, 0, 5], ![3, 6, 4, 1, 0, 5], ![2, 6, 4, 1, 0, 5], ![6, 2, 3, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 94 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16709)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 3, 2, 0, 5], ![6, 3, 4, 1, 0, 5], ![6, 2, 4, 1, 0, 5], ![6, 2, 3, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 65 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16710)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 3, 2, 0, 5], ![4, 3, 6, 1, 0, 5], ![4, 2, 6, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 20 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16711)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 3, 2, 0, 5], ![4, 6, 3, 1, 0, 5], ![4, 6, 2, 1, 0, 5], ![3, 2, 6, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 32 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16712)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 3, 2, 0, 5], ![6, 4, 3, 1, 0, 5], ![4, 6, 2, 1, 0, 5], ![3, 6, 2, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 5 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16713)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 4, 3, 2, 1, 5], ![6, 4, 3, 2, 0, 5], ![6, 4, 3, 1, 0, 5], ![6, 4, 2, 1, 0, 5], ![6, 3, 2, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 91 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16714)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 4, 6, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 42 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16715)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 0, 4, 2, 3]], proof := .tail 23 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16716)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 0, 2, 3]], proof := .tail 79 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16717)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 3, 6, 4, 5], ![1, 0, 2, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 9 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16718)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 3, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 0, 4, 3, 2]], proof := .tail 23 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16719)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 0, 3, 2]], proof := .tail 79 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16720)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 3, 6, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 0, 6, 2, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 0, 3, 2]], proof := .tail 9 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16721)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 3, 0, 2]], proof := .tail 79 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16722)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 0, 6, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 3, 0, 2]], proof := .tail 8 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16723)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 6, 3, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 0, 6, 3, 4, 5], ![6, 1, 0, 2, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 1, 0, 2]], proof := .tail 45 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16724)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 0, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 3, 2, 0]], proof := .tail 96 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16725)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 0, 3, 4, 5], ![1, 6, 0, 2, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 3, 2, 0]], proof := .tail 1 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16726)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 0, 3, 4, 5], ![6, 1, 0, 2, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 96 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16727)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 2, 3, 4, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 0, 3, 4, 5], ![6, 1, 0, 2, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 0 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16728)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![3, 2, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 44 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16729)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![3, 2, 4, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 0, 4, 2, 3]], proof := .tail 84 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16730)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![3, 2, 6, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 0, 2, 3]], proof := .tail 48 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16731)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![3, 2, 6, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 48 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16732)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 6, 2, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 6, 0, 4, 5], ![1, 2, 0, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 76 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16733)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 6, 2, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 3, 6, 0, 4, 5], ![1, 2, 0, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 85 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16734)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 6, 0, 4, 5], ![1, 2, 6, 0, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 90 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16735)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 6, 3, 0, 4, 5], ![1, 6, 2, 0, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 3, 2, 0]], proof := .tail 72 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16736)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 3, 6, 0, 4, 5], ![1, 2, 6, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 90 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16737)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 6, 3, 0, 4, 5], ![1, 6, 2, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 3, 2, 0]], proof := .tail 72 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16738)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![2, 6, 3, 4, 0, 5], ![1, 6, 3, 0, 4, 5], ![6, 1, 2, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 1, 2, 0]], proof := .tail 101 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16739)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![6, 2, 3, 4, 0, 5], ![6, 1, 3, 0, 4, 5], ![6, 1, 2, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 86 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16740)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 2, 4, 6, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 0, 4, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 88 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16741)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 2, 4, 6, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 0, 4, 2, 3]], proof := .tail 70 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16742)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 2, 6, 4, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 0, 2, 3]], proof := .tail 49 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16743)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 2, 6, 4, 1, 5], ![3, 2, 6, 4, 0, 5], ![3, 1, 0, 6, 4, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 0, 2, 3]], proof := .tail 9 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16744)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 6, 2, 4, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 6, 0, 4, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 55 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16745)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 6, 2, 4, 1, 5], ![3, 2, 6, 4, 0, 5], ![3, 1, 6, 0, 4, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 55 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16746)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 6, 2, 4, 1, 5], ![3, 6, 2, 4, 0, 5], ![3, 6, 1, 0, 4, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 68 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16747)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 5, 4], ![1, 6, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 17 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16748)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![3, 2, 6, 4, 0, 5], ![3, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 17 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16749)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![3, 6, 2, 4, 0, 5], ![3, 6, 1, 0, 4, 5], ![2, 1, 6, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 95 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16750)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![6, 3, 2, 4, 0, 5], ![3, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 95 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16751)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 3, 2, 4, 1, 5], ![6, 3, 2, 4, 0, 5], ![6, 3, 1, 0, 4, 5], ![6, 2, 1, 0, 5, 4], ![6, 1, 0, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 80 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16752)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 4, 2, 6, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 93 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16753)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 2, 0, 4, 3]], proof := .tail 13 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16754)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 58 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16755)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![2, 3, 4, 6, 0, 5], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 89 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16756)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![2, 3, 6, 4, 0, 5], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 81 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16757)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![3, 4, 2, 6, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 77 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16758)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![3, 4, 2, 6, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 0, 6, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 0, 2, 4, 3]], proof := .tail 53 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16759)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 2, 0, 4, 3]], proof := .tail 24 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16760)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 2, 0, 4, 3]], proof := .tail 52 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16761)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![3, 4, 6, 2, 1, 5], ![3, 4, 6, 2, 0, 5], ![3, 4, 6, 1, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 0, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 2, 1, 0, 4, 3]], proof := .tail 16 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16762)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 4, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 35 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16763)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 2, 4, 6, 0, 5], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 4, 2, 0, 3]], proof := .tail 51 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16764)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 2, 6, 4, 0, 5], ![3, 1, 6, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 1, 2, 0, 3]], proof := .tail 24 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16765)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 6, 2, 4, 0, 5], ![3, 6, 1, 4, 0, 5], ![2, 1, 0, 6, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 60 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16766)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![3, 6, 4, 2, 1, 5], ![3, 4, 2, 6, 0, 5], ![3, 4, 1, 6, 0, 5], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 1, 2, 4, 0, 3]], proof := .tail 7 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16767)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (16640 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 16640 ≤ id.val) (hhigh : id.val < 16768) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 16640)) = true := by
  let j : Fin 128 := ⟨id.val - 16640, by omega⟩
  have hsum : 16640 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (16640 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard130
