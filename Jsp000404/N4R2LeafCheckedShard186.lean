import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard186
open N4R2RowDataReplay

-- Original cycle 00c56cc193505629cc23cad6219a057fdf5bac7c89ce8cacac3ba8a43b014905; original global index 71.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 0108f95f3ee3bdc1f885782c9cbe162df497309bf802b892f7e4ebd50ce76bd2; original global index 90.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 02a0701517cdb463ae39a353ca29a6857d58e96b84f8997d45b61a2e87c85d19; original global index 205.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 02a077d3ab40be7d36e445fc2818cf6f56f03798e77be3a81934cb37d4a396d4; original global index 206.
def localCycle00003 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0, .thetaNext 2]

-- Original cycle 03f04927cc22037b07690047cbfe4e5383827e0f70eb4031f1360432b69789da; original global index 313.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 06d5b493b499a674a148778822ceb52e6ed6a7ff72145bcc48a6396e166d65e6; original global index 564.
def localCycle00005 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 0ddb5b4800fd796fa412309c95620603b38ae35a338530a4516722c702c42e6a; original global index 1092.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 0ead7595d7d75986367f93d8ec9ea41b53cacc8a76c3f36d65147833905ca614; original global index 1160.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 0fff16458ccf9a83f55f669217ccabe95f378927f838aab56653fb5946006077; original global index 1278.
def localCycle00008 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 1021ce8d0b31c021ba762e85130810b5ed837c8a1b55343dddf35483bf1c05ee; original global index 1296.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 10de908c5fbf11c8b64cf0ae890da27c727c4155f062e03172a4d6a9a836507f; original global index 1353.
def localCycle00010 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 138bfa98cd9fe059c720c960a1a1f712df5fcf2d520fb8fe5e36451667cfec4e; original global index 1540.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 174b3887adb68770f3910a5dcd4097f6807cda7e86b94cb7fd6bdc0724f15078; original global index 1832.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 1a16fe10eaa93865fef550e2ec0b0b3dfe7a3d8b05bdd91a41e992802448f74c; original global index 2036.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1b1ee2628af8414f81f0436cf1a6d9db13631c74c39d6c4d223fbd2ba4a20ad7; original global index 2098.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 1b269ca06036966beeef4062d862717929d1a7fc6978034bfde80a6d120968a4; original global index 2101.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 1 3, .distance 1 2, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 2, .triangle 21 0, .gapLower 1 1, .gapLower 2 0]

-- Original cycle 1db04f162e043bf0b54561783ab7cf803493d0e2528a65461c6b14fbf1b4593f; original global index 2284.
def localCycle00016 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, 0, -1, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 204fd9b771464cac536f53e1780b413e2b2ab6783e78eeeb5ef75695a79fcae8; original global index 2474.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 20bf91abcd904375313157122cc09084d1aa8e3ba86b897afe55f8e89330aaf1; original global index 2510.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 2249361fdff1232e8152b924e7dc32b22c1a43cc37d807b44aec75d86bfff926; original global index 2625.
def localCycle00019 : Cycle where
  length := 5
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Original cycle 262471a8c646934335e917df5e2cfc0d7f69c7cbb79d1070a080c0e6df76c681; original global index 2922.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 0 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 4, .triangle 12 0, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 27dec3ba2248addcf6d614f3862d1d7e1eba3ef710a19bbbdfae425dc8afa5ca; original global index 3049.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, 0, -1, -1, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 2b368a3c726666323951005391be9d4de92fc1aa46031161451c4ec1ee63d65d; original global index 3299.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 301e46349ccf8684d81062620442cce708f4117d831339ce0de3ec49c5951983; original global index 3667.
def localCycle00023 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 32e7962377f2ccac526f3b8f419cae1d23cd0a4698b0a04be4a10fb904b760fc; original global index 3899.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 34ba42bc97fc1c4d75b8c2e12810225ba2f3ca8deabb8065c1d236df31649272; original global index 4037.
def localCycle00025 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .gapLower 3 0, .thetaNext 2]

-- Original cycle 35dd04757cd257e8e26b4e269df1465912dfea073a2189accf24c5a9c88a3c98; original global index 4132.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 3, .triangle 21 0, .corridorLower 3 6]

-- Original cycle 366de7b69bef13d890097cba813a0c10b2cc61b7d37a1128902ec19a433d0431; original global index 4180.
def localCycle00027 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 36b5d2d49ef8062052ab9c456549a19117d58d3be668881373430b04e893f783; original global index 4206.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 20 0, .triangle 21 0, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 383d9f25ca8dfd101e868f8695cf5a414c9710e1bbdedb91592d2e2ad8e82a24; original global index 4315.
def localCycle00029 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 3ccf9656b9f426be18e48dcc5b4075d16ed2177634a99bd398fcf674fd70c9dd; original global index 4714.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3ef234a0812e41873d0e948baa1492af58d2e4d15380b0e2384aace9e70a74b4; original global index 4865.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 419e40452fda6d3a47bea2d1cba38f9cd505a2e7550afc27ade8c936e242fe98; original global index 5059.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .gapLower 5 2, .gapUpper 1 5]

-- Original cycle 4311faf6cd2eec5c4562250c5b86ec1b5ff4eee090eafc51ed2cc14e4f14c84c; original global index 5177.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 47b5802c9931106813c815084e076abad7200437335c9a5e1f151f1ba660e6ee; original global index 5553.
def localCycle00034 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 4e5a37065c57186862b9c1beedf0a15f2bc57332d09cc07421803e7d83cfa988; original global index 6084.
def localCycle00035 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 547549c53101200969a94dda7858b6d9f91843e7680e867a529c339049c2c8e0; original global index 6542.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 19 2, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 54ac56a2510d6a046ae403d9f2a5ec019b8d6fa348d1a704a51fb179703c3972; original global index 6559.
def localCycle00037 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 560a634e135604c2fc36dab81424402e853411dc9cc577eb17e5035bba716d6c; original global index 6673.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 2, .gapUpper 1 5]

-- Original cycle 58a39efb6bc8a8d21a87c8e64b86b791ca01d2e5e702de9f8c0b491a74df7b22; original global index 6877.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![0, 0, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 22 2, .gapUpper 1 5]

-- Original cycle 61e11921070ba6cc71fda671a6d3df69259396661267c57986e159a9a45f94ad; original global index 7641.
def localCycle00040 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 652da5c73546a4e7add1b40da520b1809faea56f50bc1dbf8ab1b269a69cb4e1; original global index 7871.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 0, .thetaNext 3]

-- Original cycle 6cd8d0e81206183f168d3de5da62669027d53e9b053ecb1ea7509739c557a253; original global index 8469.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 6ce5c7661c77b36e988a5011f3523a784b8f50f1bbd04ec5608d2c477f166e26; original global index 8473.
def localCycle00043 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 32 0, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 6cf21c29d7f1b32b6152609bceebcacdc4a6c9ef5cf22d50bb74debdd3de7d7d; original global index 8476.
def localCycle00044 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Original cycle 6d0926706e1a87fe9d806da69d951e897ba46e3b4095417a32a1436343e372b9; original global index 8479.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapUpper 1 5]

-- Original cycle 6d976039e5b1b342ff741324082df26b6bccba228618371066375af8ca1155bc; original global index 8518.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 73f7234b0de8b30c9a342f14a00f77f7108ecbfcefd5d78108656db01e902dae; original global index 8995.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 748a7b88282cdfd6684999c2e74a79c72ae6aca536d37479c46aaaee7ed20163; original global index 9032.
def localCycle00048 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle 74d6b221fbf553712d7cfb6924da6ca9d7d73e643fae32b38e29d5315aaf83ad; original global index 9051.
def localCycle00049 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 75e9e20a1d855855d35c89b42ca97f6801c0740d23b97a353e0c1a506731cead; original global index 9138.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 2, .gapUpper 1 5]

-- Original cycle 78f2c2b403e35b83beb1778bc67b49b35405f9aa1604cbea6eaf781fd5b0ed66; original global index 9357.
def localCycle00051 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle 7b46fca3516ebafb7fc16260a12a3a6e97a30e3ac46faa306a45d87fe36050ab; original global index 9546.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .gapLower 2 0]

-- Original cycle 7ed56574deab9252dabc1a2c1e0d82b929d8ac566f69e561c9beb527d0151108; original global index 9849.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 7f619fc9fe428e6fa49936e31edafe989cb142aa2424d298efc93a7bda99ecab; original global index 9877.
def localCycle00054 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 8348083d0cdd985c02d91d074caacd973efa4807b309bc6c8c670611b1f30e67; original global index 10177.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 34 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 86aaf3b84403566038e10215a258dddaafdf6251ab6e2600ce08f4aefd834b2a; original global index 10443.
def localCycle00056 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, 3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 0 3, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle 879efef67006e3bf82a0ea33ce670fcef438c23801134cce152810a2548a408a; original global index 10516.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 8b2de91b7f0861fb066860ca99dd883c79faf652659e30865eaaa3037b018a55; original global index 10782.
def localCycle00058 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 4, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 90833ce3c4eb98cbfaec86ac97d405857a2864c751b2356a24f3dda142fe60c6; original global index 11185.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .gapLower 2 3, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 91782117865e90ebaa83d74df1f951746d5351c484532bff969c45ed2e3caa90; original global index 11267.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle 95e7800943ca16e3d984eca27a9daf369830277ba50ba8206b66b0424ce5d629; original global index 11655.
def localCycle00061 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 97db719d4f68d5b311c9a152f3288c54f16d508172bb091ec4a86f9005e5cd83; original global index 11794.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 9e57774c1ae29f14e4132289c4abacb8b9b9ff95c07984710f155ab85d3dea8b; original global index 12327.
def localCycle00063 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle a5d423928ab1583291b01bb194e662416c00e6559cffb1b4846471334348efc4; original global index 12882.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a716ae849007ad44cc60eed05ae9ff20d606c8dad59b65e889dabfef81827cde; original global index 12988.
def localCycle00065 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 33 1, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle abf3d39038920250092bbf20c40dd96650e91c5eceb5fee032f795e2551631fd; original global index 13396.
def localCycle00066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 5, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .gapLower 5 2, .gapUpper 1 5]

-- Original cycle acaafb34dbd435263a4c1445362cb832ab1384014648482a1bcb15aac264d688; original global index 13462.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .corridorLower 1 3]

-- Original cycle af13eeb26cc77bdf5cba684ed998d8013e72b12f6650f0f5e71764e1102e8d57; original global index 13670.
def localCycle00068 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .gapLower 4 1, .gapLower 1 2, .gapLower 3 0, .thetaNext 2]

-- Original cycle b175c1482e068659ddd0f8b50200cd30a0c2ce2e39351bc06f2cc9e285c28543; original global index 13868.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle b76dc23a4f1ecb9606b9054cd24166f46b5b5144ba9fdb619ee938bb4166c9be; original global index 14316.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, 0, -1, 0, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle b8225d767988d692ba4cc69f74112cd7cc69f791614b1208a95896d2d6222c5a; original global index 14364.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle ba03ac4d23fef8d74991d1a01bdf1512f804fe21c92647b0da22cca6293c1e34; original global index 14525.
def localCycle00072 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 31 0, .triangle 22 0, .gapLower 1 3, .triangle 21 0, .corridorLower 3 6]

-- Original cycle bac3f06c01413226f5eb19c460852f7e3e730d6453aff9d2d58f99ba08cad3af; original global index 14587.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0, .thetaNext 2]

-- Original cycle c126839d7a45fec4c8098d6047f59839bf8cc00be03af9fcbab653cef84c3105; original global index 15077.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle c41ea2c9827f855b9ff41273a61d42b2da614ce2467a9606baa0a5e16a57389b; original global index 15298.
def localCycle00075 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle c58cdfb4c313964de8badceeed1d0f6dc8d3dfbf11b9a16f538841c7cee9a4a6; original global index 15411.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle c964d7a3588a456d312f869766278fd777ab43e904b69ee0fcaf239835a104b8; original global index 15742.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 2, .gapUpper 1 5]

-- Original cycle c980a6167e8bffd7899b2c7e499588f4870c821f0ac2acbf47118011134ba29a; original global index 15756.
def localCycle00078 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle cc554b70291c35e310ef631bc88702829ad385cbbd0748a646b77ae13ca7f5f0; original global index 15970.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, 0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 2, .gapUpper 1 5]

-- Original cycle cfec36ab91694b96ca41e03eb29d97e5ad14e8dff18572ddef21ce9c9ceefdce; original global index 16224.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle d049f3bdace13180adc25cb4db735f89847bf2564706eb013b3d6fc1fbe22d09; original global index 16257.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle d0e2caefe8776597ac8af7eab60e75eae44a69985e0ce54b8cc0e719dd745825; original global index 16308.
def localCycle00082 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 20 2, .gapUpper 1 5]

-- Original cycle d1753aca160abda326de3d9af0bb0a2d22f52d5e57c86d94c8e694a4b1b655c4; original global index 16350.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle d2742809602cc0ae68ffb17aa8742244b932509afc9f089c184d851c9d2e22ea; original global index 16425.
def localCycle00084 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 3, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle d53f0a08050c543ba7fc264cba5f29766f2f814d3111a86648d08ef41b877a2b; original global index 16642.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle d7e87cc1e3931a2ab3daa81b2f9f162c0f06b013461f43af5e170224291ea3ad; original global index 16846.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle d83c0ba0cfa0a03aa4b09d694daf6eb8a209e0e228a385317adfd90b03f2fe0b; original global index 16879.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 3, .triangle 21 0, .corridorLower 3 6]

-- Original cycle db6f148fa92a53d30f7a36058afdb2ca43a3de5a83bb5cbcd4bcb73cb1f5f8c7; original global index 17151.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1]
    constant := ![0, -1, 0, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 20 2, .gapUpper 1 5]

-- Original cycle dd270dac6ea72aef874401ecc2073c45f01003fcd1bee577c3578410de54949f; original global index 17290.
def localCycle00089 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle dd27609f383222251f335cbbb58d69a6c3940f65ab5dbb6f4d01a5588231c900; original global index 17291.
def localCycle00090 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Original cycle e3042baa074f680f73ca9883b2f7637a34aec8c126e18d992f5329b996d1fbfc; original global index 17753.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle e62651e04baad132c46030e8460229407e7050a4da18471e5502d628ad2382a0; original global index 18011.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 32 2, .triangle 27 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle e64565852ad728282c973ebfae65395151f9500f4103bb5da16255bedf07cdee; original global index 18018.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 5 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .gapLower 1 1, .gapLower 2 0]

-- Original cycle e9f2c2be92bff50fa285296efdecd76b313a8e843845caea8b78f002b711a188; original global index 18278.
def localCycle00094 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 29 0, .gapLower 2 3, .triangle 26 0, .triangle 31 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle eeac164926ed7b6ac27e117527bc07ba155992b987f492497c945e350fedc4bb; original global index 18627.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 4, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle f0a964becd18f1e8d6bc3438f64a0c3c0145739ca1e58ed92308b8d23c60f027; original global index 18769.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, 0, -1, -1, -1, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true, true, true, true] }
  origin := ![.triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle f1436b9903b81d175d29e91141f9408ffabdcf13a8e281656941c3fd378272a6; original global index 18814.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .corridorLower 1 3]

-- Original cycle f237505e655e9a5677fc78fb8b3cc31568aa6d0f9d601d373474361f594f8dbb; original global index 18891.
def localCycle00098 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 4, .distance 0 1]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 19 2, .gapUpper 1 5]

-- Original cycle f52c506e6c823eb3e667b9b36882d5ee095ad872780a6ddd3bb73f8335ec4539; original global index 19111.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, 0, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle f5c8b1c93eddc49f64ae88e105050d34c48ab2b76ccefa0dfd08d764b1ab13dd; original global index 19175.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 31 0, .triangle 34 2, .triangle 29 0, .gapLower 2 2, .triangle 15 0, .corridorLower 1 2]

-- Original cycle f6e01659b11f90e06b263b8dc97de2a3e13d4fce59b316e1d1b8e6a8fea479cc; original global index 19256.
def localCycle00101 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle f9394c8de2a08a5eba2135b7162a43c502761769c73d364d92c5fa1ce8cbf81a; original global index 19437.
def localCycle00102 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 0 3, .distance 3 4, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 3, .triangle 9 0, .triangle 25 0, .triangle 26 0, .triangle 20 0, .triangle 21 0, .corridorLower 3 6]

-- Original cycle fb648d014d4e323d12547ebe0403f791f39d0f382640eba94ed0cca26154c2c7; original global index 19620.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle fe4931fbf340d29d0bdf3f1b5e6f1f1feb04118d7297609102527a9b3b31fa6c; original global index 19878.
def localCycle00104 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 5 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 0 4, .triangle 12 0, .triangle 28 0, .triangle 16 0, .corridorLower 1 2]

def library : Library := fun id => if id < 52 then (if id < 26 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 19 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))) else (if id < 22 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)))))) else (if id < 39 then (if id < 32 then (if id < 29 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 35 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))) else (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))) else (if id < 45 then (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)))) else (if id < 48 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))))))) else (if id < 78 then (if id < 65 then (if id < 58 then (if id < 55 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))) else (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))))) else (if id < 71 then (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)))) else (if id < 74 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))) else (if id < 91 then (if id < 84 then (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))))) else (if id < 98 then (if id < 94 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)))) else (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 17 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23808)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![1, 6, 5, 2, 3, 0], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 2, 3, 0]], proof := .tail 7 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23809)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![1, 6, 2, 3, 5, 0], ![1, 6, 2, 3, 4, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 96 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23810)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 4, 0], ![1, 6, 2, 5, 3, 0], ![1, 6, 2, 4, 3, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 62 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23811)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 3 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23812)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![1, 6, 5, 2, 3, 0], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 74 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23813)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 4, 6, 0], ![1, 5, 2, 3, 6, 0], ![1, 4, 3, 2, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 48 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23814)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 6, 4, 0], ![1, 5, 2, 6, 3, 0], ![1, 4, 3, 2, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 94 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23815)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 3, 2, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 45 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23816)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 42 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23817)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 50 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23818)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![1, 5, 6, 2, 3, 0], ![1, 4, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 68 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23819)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![1, 6, 5, 2, 3, 0], ![1, 6, 4, 3, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 6 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23820)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 6, 0], ![1, 3, 2, 5, 6, 0], ![1, 2, 3, 4, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 49 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23821)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 5, 6, 0], ![1, 3, 2, 6, 5, 0], ![1, 2, 3, 6, 4, 0], ![1, 2, 3, 5, 4, 0]], proof := .tail 27 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23822)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 5, 6, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 5, 0], ![1, 2, 6, 3, 4, 0], ![1, 2, 5, 3, 4, 0]], proof := .tail 84 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23823)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 5, 0], ![1, 6, 2, 3, 4, 0], ![1, 5, 2, 3, 4, 0]], proof := .tail 23 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23824)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 2, 6, 5, 0], ![1, 6, 2, 3, 4, 0], ![1, 5, 3, 2, 4, 0]], proof := .tail 70 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23825)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 6, 2, 5, 0], ![1, 6, 2, 3, 4, 0], ![1, 5, 3, 4, 2, 0]], proof := .tail 21 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23826)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![1, 6, 3, 2, 5, 0], ![1, 6, 2, 3, 4, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 16 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23827)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 2, 5, 6, 0], ![1, 3, 2, 4, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 12 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23828)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 2, 6, 5, 0], ![1, 3, 2, 6, 4, 0], ![1, 2, 3, 5, 4, 0]], proof := .tail 55 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23829)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 3, 6, 0], ![1, 4, 5, 2, 6, 0], ![1, 3, 5, 2, 6, 0], ![1, 3, 4, 2, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 40 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23830)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 3, 6, 0], ![1, 5, 4, 2, 6, 0], ![1, 5, 3, 2, 6, 0], ![1, 4, 3, 2, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 51 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23831)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 5, 6, 0], ![1, 3, 2, 4, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 12 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23832)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 5, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 6, 5, 0], ![1, 3, 2, 6, 4, 0], ![1, 3, 2, 5, 4, 0]], proof := .tail 2 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23833)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 2, 6, 5, 0], ![1, 3, 6, 2, 4, 0], ![1, 3, 5, 2, 4, 0]], proof := .tail 79 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23834)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 2, 6, 5, 0], ![1, 6, 3, 2, 4, 0], ![1, 5, 3, 2, 4, 0]], proof := .tail 101 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23835)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 6, 2, 5, 0], ![1, 3, 6, 2, 4, 0], ![1, 3, 5, 4, 2, 0]], proof := .tail 38 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23836)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 2, 5, 0], ![1, 6, 3, 2, 4, 0], ![1, 5, 3, 4, 2, 0]], proof := .tail 21 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23837)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 2, 5, 0], ![1, 6, 3, 2, 4, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 71 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23838)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 6, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 5, 2, 6, 0], ![1, 3, 4, 2, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 40 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23839)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 4, 6, 3, 0], ![1, 5, 4, 6, 2, 0], ![1, 5, 3, 2, 6, 0], ![1, 4, 3, 2, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 51 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23840)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 5, 6, 2, 0], ![1, 3, 4, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 77 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23841)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 3, 0], ![1, 5, 4, 6, 2, 0], ![1, 5, 3, 6, 2, 0], ![1, 4, 3, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 60 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23842)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![1, 5, 6, 3, 2, 0], ![1, 4, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 43 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23843)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 5, 6, 2, 0], ![1, 3, 4, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 5 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23844)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 4, 5, 6, 2, 0], ![1, 3, 6, 5, 2, 0], ![1, 3, 6, 4, 2, 0], ![1, 3, 5, 4, 2, 0]], proof := .tail 1 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23845)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 5, 2, 0], ![1, 6, 3, 4, 2, 0], ![1, 5, 3, 4, 2, 0]], proof := .tail 99 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23846)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 5, 2, 0], ![1, 6, 3, 4, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 91 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23847)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 5, 4, 6, 2, 0], ![1, 5, 3, 6, 2, 0], ![1, 4, 3, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 67 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23848)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![1, 5, 6, 3, 2, 0], ![1, 4, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 43 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23849)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![1, 5, 6, 3, 2, 0], ![1, 4, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 73 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23850)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![1, 6, 5, 3, 2, 0], ![1, 6, 4, 3, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 75 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23851)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 4, 6, 5, 0], ![1, 2, 3, 6, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 2, 3, 4, 0]], proof := .tail 103 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23852)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 2, 6, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 2, 4, 3, 0]], proof := .tail 31 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23853)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 5, 4, 0], ![1, 2, 6, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 1, 2, 4, 3, 0]], proof := .tail 100 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23854)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 3, 6, 5, 0], ![1, 4, 2, 6, 5, 0], ![1, 3, 2, 6, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 2, 3, 4, 0]], proof := .tail 23 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23855)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 5, 0], ![1, 6, 2, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 86 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23856)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 5, 4, 0], ![1, 6, 2, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 18 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23857)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![1, 6, 5, 2, 3, 0], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 61 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23858)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 2, 6, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 3, 2, 4, 0]], proof := .tail 29 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23859)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![1, 6, 2, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 90 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23860)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 4, 0], ![1, 6, 2, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 97 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23861)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 4, 6, 2, 5, 0], ![1, 3, 6, 2, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 3, 4, 2, 0]], proof := .tail 54 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23862)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![1, 6, 3, 2, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 83 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23863)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![1, 6, 5, 2, 3, 0], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 39 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23864)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 4, 6, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 2, 6, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 1, 3, 2, 4, 0]], proof := .tail 104 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23865)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 1, 3, 4, 2, 0]], proof := .tail 54 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23866)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 82 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23867)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![1, 6, 5, 2, 3, 0], ![6, 1, 4, 3, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 32 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23868)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 4, 3, 0], ![1, 4, 6, 5, 2, 0], ![1, 3, 6, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 1, 3, 4, 2, 0]], proof := .tail 88 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23869)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 4, 5, 2, 0], ![1, 6, 3, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 25 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23870)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![1, 6, 5, 3, 2, 0], ![6, 1, 4, 3, 2, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 66 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23871)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 4, 5, 0], ![6, 1, 2, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 92 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23872)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 5, 4, 0], ![6, 1, 2, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 63 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23873)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![6, 1, 5, 2, 3, 0], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 4 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23874)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 4, 5, 0], ![6, 1, 2, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 33 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23875)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 4, 0], ![6, 1, 2, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 59 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23876)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![6, 1, 5, 2, 3, 0], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 19 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23877)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![6, 1, 5, 2, 3, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 80 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23878)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 3, 5, 0], ![1, 6, 4, 2, 5, 0], ![6, 1, 3, 2, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 8 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23879)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 4, 5, 3, 0], ![1, 6, 4, 5, 2, 0], ![6, 1, 3, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 95 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23880)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 4, 5, 2, 0], ![6, 1, 3, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 15 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23881)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![6, 1, 5, 3, 2, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 11 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23882)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 4, 6, 0], ![5, 1, 2, 3, 6, 0], ![4, 1, 2, 3, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 57 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23883)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 6, 4, 0], ![5, 1, 2, 6, 3, 0], ![4, 1, 2, 3, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 57 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23884)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 6, 5, 4, 0], ![5, 1, 2, 6, 3, 0], ![4, 1, 2, 6, 3, 0], ![1, 2, 4, 5, 3, 0]], proof := .tail 30 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23885)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 2, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 57 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23886)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 6, 5, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 2, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 30 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23887)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 81 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23888)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 6, 2, 3, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 64 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23889)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 4, 6, 0], ![5, 1, 2, 3, 6, 0], ![4, 1, 3, 2, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 10 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23890)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 6, 4, 0], ![5, 1, 2, 6, 3, 0], ![4, 1, 3, 2, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 53 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23891)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 3, 2, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 45 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23892)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 89 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23893)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 50 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23894)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![5, 1, 6, 2, 3, 0], ![4, 1, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 41 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23895)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 3, 6, 0], ![1, 5, 4, 2, 6, 0], ![5, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 6, 0], ![1, 2, 3, 4, 5, 0]], proof := .tail 47 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23896)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 4, 6, 3, 0], ![1, 5, 4, 6, 2, 0], ![5, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 6, 0], ![1, 3, 2, 4, 5, 0]], proof := .tail 34 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23897)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 4, 3, 0], ![1, 5, 4, 6, 2, 0], ![5, 1, 3, 6, 2, 0], ![4, 1, 3, 2, 6, 0], ![1, 3, 4, 2, 5, 0]], proof := .tail 93 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23898)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![5, 1, 6, 3, 2, 0], ![4, 1, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 43 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23899)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 5, 4, 6, 2, 0], ![5, 1, 3, 6, 2, 0], ![4, 1, 3, 6, 2, 0], ![1, 3, 4, 5, 2, 0]], proof := .tail 52 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23900)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![5, 1, 6, 3, 2, 0], ![4, 1, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 43 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23901)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![5, 1, 6, 3, 2, 0], ![4, 1, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 0 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23902)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 2, 3, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 57 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23903)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 6, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 2, 6, 3, 0], ![4, 1, 2, 5, 3, 0]], proof := .tail 24 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23904)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 2, 3, 0]], proof := .tail 46 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23905)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 64 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23906)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 3, 2, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 35 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23907)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 65 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23908)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 3, 4, 0], ![1, 5, 6, 2, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 3, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 22 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23909)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 1, 6, 3, 2, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 41 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23910)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 2, 3, 0]], proof := .tail 13 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23911)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 64 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23912)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 41 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23913)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 4, 0], ![6, 5, 1, 2, 3, 0], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 36 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23914)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 4, 0], ![6, 5, 1, 2, 3, 0], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 69 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23915)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 4, 0], ![6, 5, 1, 2, 3, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 44 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23916)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![5, 6, 1, 3, 2, 0], ![4, 1, 3, 2, 6, 0], ![4, 1, 3, 2, 5, 0]], proof := .tail 56 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23917)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 4, 3, 0], ![1, 5, 6, 4, 2, 0], ![5, 6, 1, 3, 2, 0], ![4, 1, 3, 6, 2, 0], ![4, 1, 3, 5, 2, 0]], proof := .tail 98 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23918)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![5, 6, 1, 3, 2, 0], ![4, 1, 6, 3, 2, 0], ![4, 1, 5, 3, 2, 0]], proof := .tail 37 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23919)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![5, 6, 1, 3, 2, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 1, 3, 2, 0]], proof := .tail 37 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23920)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 3, 6, 5, 4, 0], ![1, 6, 5, 4, 3, 0], ![1, 6, 5, 4, 2, 0], ![6, 5, 1, 3, 2, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 76 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23921)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 4, 5, 0], ![6, 1, 2, 3, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 20 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23922)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 5, 4, 0], ![6, 1, 2, 5, 3, 0], ![6, 1, 2, 4, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 72 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23923)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 5, 4, 0], ![6, 1, 2, 5, 4, 0], ![6, 1, 5, 2, 3, 0], ![6, 1, 4, 2, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 87 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23924)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 3, 4, 0], ![6, 1, 5, 2, 4, 0], ![6, 1, 5, 2, 3, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23925)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 3, 5, 0], ![6, 1, 4, 2, 5, 0], ![6, 1, 3, 2, 5, 0], ![6, 1, 2, 3, 4, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 58 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23926)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 4, 5, 3, 0], ![6, 1, 4, 5, 2, 0], ![6, 1, 3, 2, 5, 0], ![6, 1, 3, 2, 4, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 20 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23927)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 4, 3, 0], ![6, 1, 4, 5, 2, 0], ![6, 1, 3, 5, 2, 0], ![6, 1, 3, 4, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 9 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23928)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 5, 4, 3, 0], ![6, 1, 5, 4, 2, 0], ![6, 1, 5, 3, 2, 0], ![6, 1, 4, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 11 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23929)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 3, 5, 4, 0], ![6, 1, 2, 5, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 6, 1, 2, 3, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 78 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23930)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 3, 4, 0], ![6, 1, 5, 2, 4, 0], ![5, 6, 1, 2, 3, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 41 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23931)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 4, 3, 0], ![6, 1, 5, 4, 2, 0], ![5, 6, 1, 3, 2, 0], ![4, 6, 1, 3, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 85 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23932)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 3, 5, 4, 0], ![6, 1, 2, 5, 4, 0], ![6, 5, 1, 2, 3, 0], ![6, 4, 1, 2, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 14 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23933)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 3, 4, 0], ![6, 1, 5, 2, 4, 0], ![6, 5, 1, 2, 3, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 102 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23934)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 5, 4, 3, 2, 1], ![2, 6, 3, 5, 4, 0], ![1, 6, 5, 4, 3, 0], ![6, 1, 5, 4, 2, 0], ![6, 5, 1, 3, 2, 0], ![6, 4, 1, 3, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 28 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 23935)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (23808 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 23808 ≤ id.val) (hhigh : id.val < 23936) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 23808)) = true := by
  let j : Fin 128 := ⟨id.val - 23808, by omega⟩
  have hsum : 23808 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (23808 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard186
