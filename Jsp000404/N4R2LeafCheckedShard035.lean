import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard035
open N4R2RowDataReplay

-- Original cycle 010e10086be06494810ec66b865ce6864cb9322cc5367bb1178a4a48f5c6f0ec; original global index 93.
def localCycle00000 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 8 1, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 0186eaa05d9db71c4054ac2ca523a4239c3823a92184cdc6f20919a6bbc5fbce; original global index 127.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![2, -1, -1, -1, 0, 3, 0, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 0, .gapLower 0 0]

-- Original cycle 031aa33f5ab8d4436e30a71abb2765b44b6b4fcb6728be66dc34f53ddc5e4230; original global index 253.
def localCycle00002 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Original cycle 0362224bc6cb608442cf4794a2cd945fd69d310f15ac3640ea270c1540104f15; original global index 273.
def localCycle00003 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 3 6, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 1 1, .triangle 21 1, .triangle 11 0, .gapLower 0 1]

-- Original cycle 0420c1f04bf85a5258365f5c40fe78bf45b2092b039c18cec750b1f92a177f69; original global index 324.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0422f398218f958a6a270f1eb126abf3ba752a59c2f2efbe9a5e85a9d90f1e93; original global index 325.
def localCycle00005 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![-1, 0, 0, 2, 2, -3]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false] }
  origin := ![.triangle 8 0, .triangle 29 1, .triangle 34 1, .gapUpper 5 1, .gapUpper 5 2, .gapLower 0 4]

-- Original cycle 044e2f9b4a6a79ac2d4c269d70724c87ff329beca0c6a70e9b95d89ae8b0d77a; original global index 339.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .triangle 27 0, .gapLower 3 0]

-- Original cycle 04911b1cabb647805ad1b8d0a8ff4ca8d9dc1df024e9dac77d31de7b49f48c25; original global index 359.
def localCycle00007 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 1]
    constant := ![2, 0, 0, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .triangle 11 1, .gapLower 0 1]

-- Original cycle 04a7bb4fa0af6ab7c9a3fe3374abc10213267fe447526451ba2c7aa64e56cd16; original global index 370.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 0562b48a18169373e586ad0e40d135a000a2afe6a960969e7bae717eade53210; original global index 437.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 05f6c942db87d09d0ccffa65b20e85769dcca0a58f4d78544e780e04eed923c5; original global index 497.
def localCycle00010 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0734c4cea3fb8c59f2482fb1d714544f64d7c6a92feec6b9e4a68bb43a62de41; original global index 595.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 0 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 09247a8838b73faa1587472ce09f46b2157b31c5c0ed11d5abc0e2209d12e396; original global index 729.
def localCycle00012 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0a30c3c756dc7cf4db466ce77745127220d4616cc8888b5a4a028d4e464b4cd5; original global index 818.
def localCycle00013 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .gapLower 0 5, .gapLower 0 4, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 0a7d6e768bef7dd76edcc1f896440e8fe6d59b6c387da9872160b7ca20e01c2a; original global index 834.
def localCycle00014 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 3, .gapLower 3 2, .triangle 27 2, .gapUpper 2 2]

-- Original cycle 0a8c8bf665fa7f82e360b20818204f8b15daf0dff7fa5066386efe68c48f42ab; original global index 839.
def localCycle00015 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0cb0ddbe022a8fd82866bf1937b76a7377e86afdc82be627fc6c489fb72b0d94; original global index 1005.
def localCycle00016 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0d68b5eb83a7ce3da2a8aa401cf5d9f0ac3d1df1916727f9106dd86b3d80691a; original global index 1060.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -3, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 0e0dcf95a94e86b464f51fadd03fb3b76364e7e9c5a5eba6a1f40b2969a49660; original global index 1104.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 0e307303a4a75df1c4f6b22eb7279a2f58e6a0982e9093b3a8ea29a0ec8743d6; original global index 1117.
def localCycle00019 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 3 2, .triangle 11 2, .gapLower 0 2]

-- Original cycle 0f6f8e130ab45440041dac80dd1e3d486a080d61205fa0e52a5fc6a7497ff5da; original global index 1223.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 0fa266d96e95b2135f8c70923b712f85443ef75e8746546ff65d654db4879668; original global index 1245.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 3, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 106944343f5bbd3917d07fbbb6b61d3fa3f750b57d151be069deec8dca5ef663; original global index 1316.
def localCycle00022 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .gapLower 0 5, .triangle 14 2, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 10df6a609f99f9d3130edd3bacdfc3fcde55409e574d9c099b54806969fbed5f; original global index 1354.
def localCycle00023 : Cycle where
  length := 5
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 2, .distance 0 6, .distance 0 3, .theta 0]
    constant := ![2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 6 1, .triangle 8 2, .gapLower 0 2, .corridorLower 0 3]

-- Original cycle 119faee29953a42e5100ee118cfc719a67faee20cd28149c95f645c958790e21; original global index 1408.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 1210373bebb66e41c06695f34397571f0bdc5512fe1e8f8a06eea6da67dee864; original global index 1442.
def localCycle00025 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 0 4]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 12 2, .triangle 14 0, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 1380958839af21a9214ebf797dd1c088d473104f72f1831c92af4e05252a0b24; original global index 1537.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 1415578d5a910e3ef4f0c8706afc5d584cae31774ead1d2c9ae519ef0e7fa04c; original global index 1584.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 143feccba370264751c330f31ec04a8d66cc1fff6a70d2856392a2b6f0b33d9b; original global index 1599.
def localCycle00028 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 14c05e913c1b86a8b24e439b53e1bdba8fa5a27db4518a9b386eb4db73b3e156; original global index 1645.
def localCycle00029 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 6, .distance 0 2, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .gapLower 0 5, .triangle 8 1, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 14c6cf14006de1ad79cdd942539c51ec34578e036009d18b4ef7ebbc9c648e6a; original global index 1646.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 4, .triangle 7 1, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 14ffec48bcf7749a94e505c416901be886eb519ca1faa02b31d8a3cf95a5a0d1; original global index 1665.
def localCycle00031 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 34 1]

-- Original cycle 181e6ad44a3244af8536f4097cf54417c964dc3369716934798e913efd73860c; original global index 1886.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 186918b7b25472ec60bb508d0f63ce26826432ec65db8cde39f7e9c506d0cff7; original global index 1910.
def localCycle00033 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .gapLower 1 4, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 19e0892124ea72e175cdcafc4ea288eea95dc8fbc44807800b20a157f9de382b; original global index 2017.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 12 2, .gapLower 0 4, .triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 1a19b5eeca34fd18134298e5dd9f80fdf44170f660ccd0b4912807528bee6256; original global index 2038.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 1a443c272c200510e4f5529c75f77aa77e2667fd8cc126224f8c8325c96659cd; original global index 2052.
def localCycle00036 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 1b31445b28fcfc8c2490e3c342c38c33d59ee62568f62285ea67cde171b56716; original global index 2105.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 1c550dd6bcef85a1504efad0aa6474e2b1c13af64231757cadea2170cee28e41; original global index 2177.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 1c7bd374dcdcac8a9b270cd2b10816ad6e9fdf185f5d4604dfd4f317ed7be4de; original global index 2186.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 3, .triangle 14 0, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1ed9b5089426b83901c48d4fbc29913e2d8a210e0263d80f1b213d0ef168a3bc; original global index 2369.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 1fedb1fe19a464d2d3c15005995b011017b46c455acb39214c9eb36088f4df95; original global index 2451.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 0 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 21e0a118a2810e947046755ebee0e21c7ce9b5dbd0df3023e0275728db08b6e9; original global index 2596.
def localCycle00042 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 227f6a493c616b231f78ecc2b6fac89880ba8c4142ef628dace8663a3a4715c1; original global index 2640.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 22d67ee44a7705e5224bb51e42c68e85211a97606827e8b5368dadeec08266d4; original global index 2665.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 22fda38e0238708bd673c17927a0e54e5103cade2a4a4fac2bb18fc00a0d1e99; original global index 2685.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 24a5b26f178dc07bcf50d950a975e2e2c0b03f75d4d9faad56ce0e744613d778; original global index 2810.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 3, .triangle 29 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 25212415a47dbc114ea76e80ebedfd845628c24b00ba7cafe87f492c213cb3c2; original global index 2854.
def localCycle00047 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2]
    constant := ![4, 0, 0, -1, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 6, .gapLower 4 4, .triangle 22 2, .triangle 24 0, .triangle 14 2, .gapLower 0 4, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3]

-- Original cycle 27b7f58e4431eb9b7c5d9e5361af61e83c6ce297d7213398072c34375ef8eccc; original global index 3032.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 12 2, .gapLower 0 4, .triangle 8 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 28ea3b17ee23b9259115b47a07808e419c931e7b93dca6c580d1de91b6b2e42c; original global index 3128.
def localCycle00049 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 6, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 13 2, .gapLower 0 4, .triangle 7 1, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 2a5e02c26e3e4bb66b97efd944f6c7cec38383ba6953d3ba462e2af7a0f9e841; original global index 3230.
def localCycle00050 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 2b1ae457fec9da86dfdaf8013b2537c6d2a17572ff6e791dc3dfd309e756a582; original global index 3294.
def localCycle00051 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .gapLower 0 4, .gapLower 0 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2b88dc0ccc961d0056617ff0fc0b375a62f4d492ed50b1cc7c27928d4a04066c; original global index 3325.
def localCycle00052 : Cycle where
  length := 12
  data := {
    node := ![.theta 0, .distance 0 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![1, -1, 0, -1, 3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 13 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .triangle 17 1, .triangle 0 0, .corridorLower 0 1]

-- Original cycle 2c8812b28e88198787c9f00bbe232e3db3a19f6a1e2d8d746afee60b7ebf37c3; original global index 3402.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 2cde68129d50062b8b8fab6b3bd8ee52f1ed1f14b825ade054c2be4161a720b0; original global index 3428.
def localCycle00054 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 6 1, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 2d942570c5ab7b6d73c630b81823f53d7363c69367e200d6e27b161c5984543d; original global index 3472.
def localCycle00055 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 5 2, .triangle 14 2, .gapLower 0 4]

-- Original cycle 3078f9de535d0a48b1b57befbc7a08bfc987874bccb5b2171b8c7e7d17f8ffb9; original global index 3690.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 3087c5f85c6335d77f7a20dab94f3a436073b2277604f9c4f2e232dbf0f2670e; original global index 3696.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 308ba4dd9e6b3aa853c01e5058cd5e6b15dff18e1156ffdf66f1db2747603c66; original global index 3698.
def localCycle00058 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 30e6ce3a7a0bad9350fc1fd4f0ed82642044bdc0d0d27d84955bb60bc269c0b7; original global index 3729.
def localCycle00059 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 21 1]

-- Original cycle 313468ba3baa9363d2c5e6754669dfe270c50de63497a00173f0ff293f3251e2; original global index 3750.
def localCycle00060 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 3, .triangle 11 0, .triangle 27 2, .gapUpper 2 2]

-- Original cycle 31cc94716cccf89feb16519a1e367e32494268cbedcfebe34a92d6e2e5d32fc9; original global index 3804.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 1, .gapLower 0 4, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 32ce5f7a9e7268c6af2f3ed90b15354fee861401e4457f0ec588f4185a10b4b6; original global index 3891.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 3401a4ac5f2e87583f544ae5a48964f6f6bbbf6aba082b0bc7f841afe5b95cef; original global index 3983.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 35b3185e2b3085d7b4f5395f692d86d16cf1dc3d330f3aeca4ca6979a566f1c7; original global index 4113.
def localCycle00064 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 2, .distance 0 6, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 6 1, .gapLower 0 3, .corridorLower 0 6]

-- Original cycle 368df2626ca45afa1a79b8eae932b2ba95e23423dce56dea6e2b868298b9f46d; original global index 4190.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 37e3a7c75dcc6f21dc37ec68751eb3377060221502fce025e2e79b82c6d4b215; original global index 4296.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 0 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 38787abb9286cd44e03ba3c139715695635520f6f8509916557fb127ad358c36; original global index 4348.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 399183be39d113a17b3a05eab3a841a17c5bc4cdda4ed3b2cce0d9718629ce99; original global index 4436.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 13 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 3b8156a6623321f664fb924420a6268e54fcb87141870df1422e7d968514bfb3; original global index 4598.
def localCycle00069 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 12 1, .gapUpper 4 1]

-- Original cycle 3b9d0ddd0736f20f79cc356b276d2a83c7cca4e45debb4361ed76b4c56f29b61; original global index 4606.
def localCycle00070 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 2, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3be1738c091ede30b9c3be14e9ac957e0bdf29e57a726e7d79980bfbff96e6c3; original global index 4637.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 14 0, .gapLower 0 3, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 3c8fa76e1eb037596aaa547a936fa82c42a1704b4af169a0e93a1448c99396ea; original global index 4697.
def localCycle00072 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 3cc65bb4d27c1b25a5de343b21592639526c06b764333a52a642dd224f1aba0c; original global index 4713.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .triangle 4 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 3cd0571f003fa7abb4cf73a3b148a2a649eb0ce633048d50fd3ed28890102f67; original global index 4715.
def localCycle00074 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3d2151293512b5b6c990e3380cde994137c114eb884534c387736364e3641b6d; original global index 4737.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 3d3c71d4bc119d34e915c3bfea2ecaa388709dd659f8504f12f71202ac9d15aa; original global index 4742.
def localCycle00076 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 3d4b1120274a2630565f6b9e7861c2333a5d8be69400e96b476f947924925b67; original global index 4748.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 6 1, .gapLower 6 0]

-- Original cycle 3da39e11ff9659b63745af546960cb5ff182923b758d546117bcafaa32bf9d6a; original global index 4771.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 14 2, .gapLower 0 4, .triangle 3 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 40ac7453c8a465d646d441af02b925c6e570d4e91e0d5a8e77fcdc4d09083fe8; original global index 4997.
def localCycle00079 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Original cycle 40be53d2f4aaea1e0bb663619090947492486f38614bd015e60e9c32da4292c2; original global index 5002.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 42fce581266446c68f7752962e03d978443a64f41baa42ee4c826374c494ec72; original global index 5168.
def localCycle00081 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 0 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .triangle 14 0, .triangle 34 2, .gapUpper 4 2]

-- Original cycle 439997874d68aceb155d82a2a0f39a687e2ceed398a8a0302ae6a87a599f1b37; original global index 5227.
def localCycle00082 : Cycle where
  length := 4
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 2, .distance 0 3, .theta 0]
    constant := ![2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 6 1, .gapLower 0 2, .corridorLower 0 3]

-- Original cycle 43da6a6bab08286bbb08f0fcdb9e5b276da00e605f5396f75f4f39de0eb31788; original global index 5251.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 4452ac49d5e35a27ce13c265d1644ad6c77909250b63211128804b4006f2b6ee; original global index 5289.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 11 2, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle 460fd9d1d731eab3a74dd77dfe4211a1637aa8ba6ab8609bba8f001bcfa02b8f; original global index 5421.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 494e0bdc223d50784ce468ccc459158431e82b42458b4b01abfbd1fc08450317; original global index 5680.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle 49b1958c2fe73c346d8ef8c561f7d3367964162f5445c813316cfc9e6f8099c4; original global index 5716.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 14 1, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 4a0e4905aab7db1430b03903f5c4b013f65954aceb5b9c35fc535effcf5bd7c5; original global index 5748.
def localCycle00088 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 13 1, .gapUpper 4 2]

-- Original cycle 4e0fb42bbb602d0b8e896410e3738b46c89a204ed497e05d2b97236aeab224be; original global index 6058.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 6 2, .triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00090 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 50f59cf2082878443acad0ba51b769f7bc3f2b53ce2b909dc16b2f9b6ebc8572; original global index 6290.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 51134cb9230ec8e8c55137e6b071a6aa768b7a41b89a634993a56de85d43a96e; original global index 6295.
def localCycle00092 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 14 0, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 51f14d516613fd9fe9fccdce18a762db20ac585b2ae11a7322b323f7974b1920; original global index 6373.
def localCycle00093 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 0 2, .distance 0 3, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, 0, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 3 2, .gapLower 0 4, .triangle 8 1, .gapLower 0 2, .gapLower 3 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 5285ce9bde6e4012353c2785e729227129e670ea6a46228d7fab4f45c36e8974; original global index 6415.
def localCycle00094 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 52acdf1678db8893fc9004a2c0f8c9a84467ad7d34528fb9953c258e563ba616; original global index 6427.
def localCycle00095 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 14 0, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 52dd9ff2bff20480886fd8b7fd809a75518a4a8b5601d1810f7da4ac1ad74293; original global index 6453.
def localCycle00096 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 53057d94e4f1c35415a740f54029a03a954bca35dbe3e8cd62997329ca255ce7; original global index 6463.
def localCycle00097 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 54b754ea4f916f452dc928d336e16f198c100a7d842a826aa8cb5534ca823ea9; original global index 6562.
def localCycle00098 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 12 2, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 55e611bf10f5671bac3dfdf7371319c30a07aaccd331af59a0c6ac62ef91860e; original global index 6659.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, 0, -2, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 12 2, .triangle 14 2, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle 578e158cee721289aba55ae99a8d4173e3d720bbfc1c7b4bc30b5b19e004b3b7; original global index 6797.
def localCycle00100 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 58902c02faf498454b41fec2470e5a817035ca03334e3e03062c8de4fb69ec79; original global index 6874.
def localCycle00101 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 14 1, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5956e3486a6d9881d25031c885cc30c63593c5192b02b7fa306e5c1efacd7a33; original global index 6940.
def localCycle00102 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 8 1, .triangle 29 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 5aa02169559f8cd321b444c8265e669913eaffab401bd95c68862c3c6c31fa80; original global index 7054.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5c3ecec023570ace9d4fcd7651d844cef3148c3450d8dbe99a0ceda6460f1154; original global index 7182.
def localCycle00104 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 6 2, .triangle 14 1]

-- Original cycle 5f649874e71b75c382bf23e30fa425094ed335f32633f2ab1b680be4db958f16; original global index 7427.
def localCycle00105 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .gapUpper 4 2]

-- Original cycle 5fa40d1c7112f02422367e687ac0aae4c56628fb8b0e3249d87772beb0538158; original global index 7450.
def localCycle00106 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 3 2, .gapLower 0 4, .triangle 5 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 60f4918b60985f65b4f5d39376a28ca39e4ba859336a77664e173b4d31a20961; original global index 7555.
def localCycle00107 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -3, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .triangle 4 2, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 6190df88c1d0fd9242d6caebaf76e134498097a9cbff93fde86b5af6c3134446; original global index 7613.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .gapLower 0 4, .triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 63beef07e4b400fb42b5089aa4469645f4bd52b3614a55187346e226ec9d00ac; original global index 7774.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 7 2, .triangle 12 1, .corridorLower 4 5]

-- Original cycle 63f1b960907e064cf4a783a86df041a5ead99491ce26a77eb74558f3fda057c8; original global index 7788.
def localCycle00110 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .gapLower 0 4, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6593567b00a253348ab85057ca60ad2f11dd6b6e577561313e892cc6d051bd6a; original global index 7902.
def localCycle00111 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 3, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 65c93f266ea2ab1d6562c36eeebc6b2532c080f8556f57f3e1e81773b2de11bc; original global index 7920.
def localCycle00112 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 66ad46e74633233b123c2154f90d9129861544c2471a675c685c423ddeb050d5; original global index 7981.
def localCycle00113 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 67929fdc6764e50d167160d3f129fd35dfade07bba07a84a9e9864c19fd3b857; original global index 8046.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 0, .gapLower 1 3, .triangle 21 0, .triangle 11 0, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 698af1f02b84b8a00977e8b2db6cfa0a5d54747e3ac2869874f997c9fceba94f; original global index 8207.
def localCycle00115 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6a1680f5421c451d4a4cf80135e79f92aa830389581234f8ae73fe00393db344; original global index 8253.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6ac43cfe60eaa5325705c2dce90df9939a007a66d0e46dbb765dba232f65ed7a; original global index 8311.
def localCycle00117 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 33 1, .triangle 30 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6ac4b364561994212160928e68c7e6dbbd14757dd9db6a8351722e3ad94eec1a; original global index 8312.
def localCycle00118 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 2 2, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6b179b96e9c93a220e249e7654c49d2fb23172208b8e526bc2748089de0c8a52; original global index 8337.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .gapLower 6 3, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 6b871392a21a7ff6bca964ab46efbad98fb6421ff645493b3d4ebcd3b21a70e1; original global index 8371.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 6bc12d59af498df685a6da0cb1a82676cf420f840e827c0bec9a84a28181e0dd; original global index 8389.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 6c52e8b35653e2608f7c5a7067ea69774d1f2198d445956673f994666b89604c; original global index 8439.
def localCycle00122 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 6c719c316abcfe87c3a30256b9d8befafe3f4554118ef825f342f874eec93fa6; original global index 8442.
def localCycle00123 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6f07abf71490ebd876dd0219841890d8a98fc9302991703ec07f6080e8c26a22; original global index 8611.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 6f6853a1d9ab138cf636a97cb6b907cfe90f89cb7bb5ecd1e9e66f6b01d87665; original global index 8635.
def localCycle00125 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 4, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 716d992c0802d8a82d120539193fcd48e5042de226d3550588b93863b74b7415; original global index 8803.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 8 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle 72142a219ff5a856221ee55deb8b69df9ed2f0a85d0c74f7b99b7d198fb44038; original global index 8841.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 7234a882c37da328203c7260b33196fa9790dbc9f8b45275144647968f5b343f; original global index 8854.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 72fe0da38127ef77fb0f5747991fb12f87890beaac7a4176ebf096cc2a15ebd9; original global index 8909.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 73e003d20b0a04eec864dab4200a8c92bbed52efb0e7e43ceeca9774fae87a28; original global index 8986.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .gapLower 0 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 73f64205a3149c83145a88b775589ec0dee176d3d3271775d79fbceb60ca9f48; original global index 8994.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7437467c2d5366e742fc7102e77a316bebd5d8be247f8d482c773d26e91fba34; original global index 9017.
def localCycle00132 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 786a827738ec3db9719825d2619db4e5e15bd692fe51518b7dbb7b311ba6d117; original global index 9313.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 787bd61d0a716871453a2e65d987fec0cbe246f2b7cc32cdc0f952e21418d0a9; original global index 9319.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 79530a3a98d000e0023f1bf4ed550e91cf41cb1a5ec698b4be3c1eb23ddb99e9; original global index 9388.
def localCycle00135 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7bffefa1abf91a15f841d63fbf18cad0de3ee9ab6811caac68458ac4b9ae77f1; original global index 9592.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -3, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7c201a7e87a92da3584078ea1cacc7660ee0371f4b8cf000ec37f0667fbb5be5; original global index 9603.
def localCycle00137 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7cb040665a93060e8c217cd16705e864704460c171a08d20aca72afcd81d16f0; original global index 9655.
def localCycle00138 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7cce58deaa93fa8b033e4149401abf50669fd2772ee3769e5ff80bee5fa02eee; original global index 9668.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 7dcceb3f15cde7f347b0c961f7dcae254d719c8850a65709b008e0f819742e99; original global index 9767.
def localCycle00140 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 29 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7ddd83272ce547a411c9669fc5fbe955b70ef93a241f45c22867e7b6de5339f4; original global index 9775.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 0, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7f2fe59975c0e2339d10ae04612a800829f2bc71549534317d4b3674bb48ff7e; original global index 9863.
def localCycle00142 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .gapLower 0 3, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 7f57a0c36d16fbdf9733389a42cd3229b26731a62bc57a95e364bea16056abd6; original global index 9874.
def localCycle00143 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7f9f31ec96f2b71166698b78d32a5fe6fd416b3fe710be7a3028c62adb8e7f4c; original global index 9897.
def localCycle00144 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 14 0, .gapLower 0 3, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 84b7b93784d59b9d6b99f7ce4a85ebd9cd486a174e2a5044bc3b6a70cdb370f9; original global index 10302.
def localCycle00145 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8507afc2710ccd4056452517605c97a43ad444497c9329379cad24e08b64a7b6; original global index 10325.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 4 6, .thetaLower 4]

-- Original cycle 8556609be4a0db9d66e943fab768c7ae3e6cebaa8f459346b10117885ed88b43; original global index 10345.
def localCycle00147 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 3, .triangle 8 1, .gapUpper 2 2]

-- Original cycle 8604cf705b5f34a506fe383518c4414a160d1fe5427b48382bfd59266d48a708; original global index 10396.
def localCycle00148 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 8655f0b704410894d8ca22e8468a36174dc2b0fb0224773a8a9ee85201a7e31f; original global index 10416.
def localCycle00149 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 883c8f56da127469241d4adca7025cc95e976e621251ae49c4731a77efb32a3d; original global index 10558.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .gapLower 0 2, .triangle 4 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8aac7a7f30d05d06bfa2a911005396f2eb9806ca39ad60ad080f07708f08ee4a; original global index 10744.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 4, .distance 4 6, .theta 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0]
    constant := ![2, -1, -2, 2, -1, -1, -2]
    coefficient := ![1, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 13 0, .gapLower 6 0, .gapLower 6 6, .triangle 21 0, .triangle 1 0, .gapLower 0 0]

-- Original cycle 8ab9b02680de32218a31b3a952c56e4f97b310ecbdaf2fd3210fc43a2d1ec237; original global index 10748.
def localCycle00152 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 8b2b05719ebdcc8d2bd2a95d290369cfb0d424e629fad729d6e0c6f4cea1c3dd; original global index 10781.
def localCycle00153 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 1 6, .distance 1 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 21 1]

-- Original cycle 8c5c810ae6902a322cd0d2935511583ea12c10ff7c8bc318f08ec003a4fbb04e; original global index 10861.
def localCycle00154 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8ec210d9460cf03edafed2190b02916c24b3eed999f9b4c06698229c7d884b8e; original global index 11048.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 8f0fd28b18ba001419023d6c650ab653f5436eaec4aa3beeab07b49d1f10b57f; original global index 11069.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 34 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8f9299f038a17d7a0f1f05703a78c708d920aa6270d01b3e250508071d4eef46; original global index 11111.
def localCycle00157 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 5 1, .gapUpper 4 1]

-- Original cycle 9126474414e79fd09e0f63d5e3950f7be492b9060f0157ea5e6e04a1e76f9246; original global index 11240.
def localCycle00158 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 4, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9190fb8b8f75170edf0a58c1176b0952b8bcf46af821afc28cfe3c05392154b9; original global index 11277.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .gapLower 0 4, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle 91ac8848afcdced1b3630d50f437184d957080e134e55aed31c397215fc76759; original global index 11289.
def localCycle00160 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 92037d1e2a7cdc09edf74aafa11a1392155701fee053a68220adf9c67de1a3d8; original global index 11315.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 92afcafb3817b1ab2075be1ad52d53650f6562e0ceb1de79f14756d3d5f11882; original global index 11365.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 3 6, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 930bf4b019ca510eabc27643050b5c653f2ac6cd49c1708285dd74b9573292e5; original global index 11401.
def localCycle00163 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 9377d2aca9bd2b219f040215585d5334112883f2dd1edf8583d9b5bc56c869f9; original global index 11440.
def localCycle00164 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 0 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 94eca0cb7a78c1a879b3c4a62010b809f01c69a35b982dbf0c7f158eaf285450; original global index 11559.
def localCycle00165 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -3, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaLower 2]

-- Original cycle 95ef0134d1bcabd2b29edbe0cad8bab6d8ec4fc7d722ce50f702d5fc3ac42e03; original global index 11658.
def localCycle00166 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 968a3c7fa7cf468b759d6d4a5e9f68b116e8eae262e3868ae1f0074cce679092; original global index 11707.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 96ab70f24a5cf79c633a5a6ead5763726717e8039bd9860bfab8b688b2d26c9d; original global index 11713.
def localCycle00168 : Cycle where
  length := 4
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -3, 0]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.thetaUpper 1, .gapUpper 1 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle 973d196ce4cae0a238a7de1adb2afc18b1ef9ccd73e3397cca54f5f7e5038c5b; original global index 11752.
def localCycle00169 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle 97f0d2dec9a04700442b13c573ed75245f7db74cb0990753ecbb84a2c4007327; original global index 11799.
def localCycle00170 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .gapLower 0 5, .gapLower 0 4, .triangle 5 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 97f66c231a34b146831a5d032eb3cc9ee2f1c9f952375a284a60422ee4ee0d9e; original global index 11801.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 2, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 997026b3bc39def187caaf938c349d8d4d05c4cd69cabbf21529a491962d6c87; original global index 11918.
def localCycle00172 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 9997deb684478223a040bcdb8598b7f709e1992dc7686bd2d3e56d6fd59bde52; original global index 11925.
def localCycle00173 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 2 3, .distance 0 2]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 2, .gapLower 3 1, .gapUpper 2 1]

-- Original cycle 999c68a8c05fbf3a3272d299a26d6e6198fbe63ed9ba85325144ea416297bcb2; original global index 11926.
def localCycle00174 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 99b7fac89cbb94fcae131e85b417565c2829209d2793169e9bf71c8a525d591d; original global index 11934.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 5 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9b7847d6f7296669ae1bcbf5f2788a1c3b556ede9c457f16cba33901aae5c1cf; original global index 12093.
def localCycle00176 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 12 1, .gapUpper 4 2]

-- Original cycle 9b87d134fc2147c9b757a05f2f7efc04409b63d634dc1cded6fd875830b81185; original global index 12096.
def localCycle00177 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9b934faabbf74e9021ff3fa5c4b64f4705c58295137a91c589020b94b71ddcf3; original global index 12101.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 9bff84545b48bd6552206bd50d43b318fc368dcf1ad332b02f27d838d4f09b05; original global index 12134.
def localCycle00179 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9cdaa04edc282395ea17e8e0269ae0af293ce2ae95a4d92d940df58062894af8; original global index 12199.
def localCycle00180 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 9d3066941fb50ae1c8d6c1f2d7220375d144d6a78c81a8e3dcf17bfb20831973; original global index 12228.
def localCycle00181 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 2, .triangle 23 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 9dae0d1590fcfb571fd5d02e7ddeb30a46d5eeab0012783d83c45a65c5ff2bae; original global index 12267.
def localCycle00182 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .gapLower 0 5, .triangle 7 1, .triangle 8 2, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 9e0c2a98295a93f8739900473ba6fd4258dc6cc14c1ed8ae5ec194455868a7c0; original global index 12298.
def localCycle00183 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 9e142b32e24f348936f382e8ff141e65370e42424cbe49e0c28f5656b943f52a; original global index 12301.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .gapLower 0 3, .triangle 4 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 9e8007d3690c562cffe74d19d0bb80f267b904403678e6cf6f4cf858c48e842f; original global index 12344.
def localCycle00185 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 9ed8fa81144e143b5a9b7677d5fd6a454297238de947cbd020abed0db803c8fd; original global index 12365.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 9ef395cace198c712442077b9aa1c4623ad584729238d6a2955994c3e941e121; original global index 12377.
def localCycle00187 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .gapLower 0 5, .triangle 7 1, .triangle 8 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a0d6e35fba55ba9c49960e1713cb1a89b5b590a7aaa82fdb20af161a4fa3e1da; original global index 12511.
def localCycle00188 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a27d877dd367cee5f1cfb297387eebbb23a8ac1e3459d5a70a90b2d4fbe20bc7; original global index 12640.
def localCycle00189 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .gapLower 0 4, .triangle 5 2, .gapLower 0 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle a2d24fe41daccb94a2a047539690d44fb15e5048c0e5c7b29f2725edb014fe4f; original global index 12664.
def localCycle00190 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle a4667c34c421faaa3da4e497344d53ea415df2eb7c773e08437eb7f3e29aa0c5; original global index 12779.
def localCycle00191 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a4abc8ae5e4953f184d17d34568bd7f03a843fe87946386eb89424cb6e698c46; original global index 12798.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .triangle 12 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle a727d298cc669822da5e61126749bdfc286defb1a2da298008b1a73c72289fc0; original global index 12996.
def localCycle00193 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 5, .triangle 13 1, .gapUpper 4 2]

-- Original cycle a8b11692619147fd623eac940aab8fd42aa2f4ec1c1e849ab5f4bb527937366d; original global index 13128.
def localCycle00194 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle a8ba377b584f448c7018820d2da6e24514e540dcc8b34a888575b9779e5f5ded; original global index 13132.
def localCycle00195 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00196 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle a9918e24e87dd8ad115be9e6c2e5853f77417d146063e9f25ca7f9cd7aac2c63; original global index 13201.
def localCycle00197 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 7 1, .triangle 8 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle aa1913b317ac6d7198c5f2cd447c8e394067bcaa8bbb3bb440236abbaea50cc6; original global index 13243.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ac2ab8387fe4493eec16bc54075509d2ddc0f8f7cdb68d68b535100fa3da0704; original global index 13420.
def localCycle00199 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .corridorLower 4 6]

-- Original cycle aca14f55cc755032b4c4e5cfcb017cab44300e633667110ad4bf960b3f6d01cf; original global index 13456.
def localCycle00200 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 5 2, .gapLower 0 2, .triangle 11 1, .triangle 27 2, .gapUpper 2 2]

-- Original cycle ae2d9dde6112f28694591462470559eeb57a3c0c6546516bab00aadeceb2ccf5; original global index 13595.
def localCycle00201 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 5, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 12 2, .gapLower 0 4, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle afa21f2aa1822a954bf10d7012b2360dfba01ef3776e3d29cb457ea2d07ed5d3; original global index 13719.
def localCycle00202 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .gapLower 0 5, .triangle 7 1, .gapLower 0 3, .triangle 8 1, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b059012e15a2db0c02c15eb61611595656984c5983b5f6d8501abd16a890b062; original global index 13768.
def localCycle00203 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 18 2, .gapLower 6 3, .triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle b0cf9c0e87cee7b32b559c7bfb92629766b2e2a0f532775eaba45af56f5449e1; original global index 13807.
def localCycle00204 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .gapLower 0 5, .gapLower 0 4, .triangle 13 1, .corridorLower 4 6]

-- Original cycle b111c58dad9778bc2a9fe2ce6c547b0e8f62afadb2e67b17ecb7fda68f3b7d19; original global index 13826.
def localCycle00205 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle b30b61fa1251965ecd84ddf4d63bf23a703170db0e2d7b106471c640ccc06ab6; original global index 13991.
def localCycle00206 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b4c79241f7d9b02483833573302750024b1184619ef49e06bd0f2393fce91f4c; original global index 14116.
def localCycle00207 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 24 1, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle b6768a492cbdcbdd8e4b30781e524f145bf930ce8b84bf838477fe6cd94770ab; original global index 14261.
def localCycle00208 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 11 0, .gapLower 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle b822cc87a7906ca7dab56a2b23ad9171f22c8619f9e5f851919258417f8da2dc; original global index 14365.
def localCycle00209 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b94a61f4ef5a9c2a54a256650b028179500b5f4de5c6117c6dde64af93bb408b; original global index 14456.
def localCycle00210 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b9f4e8198d6a40d59a509b86c40a7cb65b1973fcd1f1a68b480eb050739e06a2; original global index 14520.
def localCycle00211 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 3, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle bb0a5c679f192f2ec7003073fa85507cb874c4626c6d18af18d105aecc6af42d; original global index 14606.
def localCycle00212 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .gapLower 0 4, .gapLower 0 3, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bb4788d4c63efebce5afe2e5da6c412d166d187a7376e814711dd67ddf86d7a6; original global index 14623.
def localCycle00213 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bbc64df594e46e06a9651911e3640a411708cfb36bfed2ce98b1483f87fa2a70; original global index 14665.
def localCycle00214 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 6 3, .triangle 29 1, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle bd01f8d573269d17c37c6096ab71efed79aad72613a349b4b24bfa8e9ffd3c5c; original global index 14744.
def localCycle00215 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![-2, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 14 1, .gapUpper 5 2]

-- Original cycle bd622e3c6b5cd4b10015676f127285e4b437ec1da0877140c232ea2873133fdd; original global index 14770.
def localCycle00216 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle bd67341476ffea9693b999bf63360bc099f56532c6a06fcbc9d699379620c3a9; original global index 14776.
def localCycle00217 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -2, -2, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 0, .gapLower 0 3, .gapLower 0 2, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle bd6cd3bfcec3e98d2c7e28e3eaaf26c5ce66c23a5ab3933ef8705a04ae282841; original global index 14778.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle bd871d10e0c3d31dabaf3a0ee60cff76cd8fd80ef6549c4262e0ac1af2f0df01; original global index 14784.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle be50aa92c2608ebc20ea0fc1783d12ff998b2898c6585c3a680a3e20e6104205; original global index 14847.
def localCycle00220 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .distance 4 5, .distance 0 5, .distance 0 2]
    constant := ![0, -1, 0, 0, 0, 2, 2, -3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true, true, true, false] }
  origin := ![.triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .gapUpper 5 1, .gapUpper 5 2, .gapLower 0 4]

-- Original cycle bea77d369c3de18fda26ff35feb083a042cb1b9467e9cf9c823802117f0cdde5; original global index 14872.
def localCycle00221 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle bec6709aa6e08199ffb3ba11510dbbddad20da7615e2d3603ad48b364ff091d9; original global index 14886.
def localCycle00222 : Cycle where
  length := 13
  data := {
    node := ![.theta 0, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .theta 0]
    constant := ![2, -1, -1, -1, 0, 3, -1, -1, -1, -1, 0, 2, -2]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 0 6, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .gapUpper 1 0, .gapLower 0 0]

-- Original cycle bed99d09b1d5bba9db1408c798a34af9ebfe13d4d47402a768ebcb5ae44f10f7; original global index 14889.
def localCycle00223 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 5, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 10 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle bee69768af5ab2eaceca05df1b7c09ad60947196b25e76eb2d8420dc666a4c8c; original global index 14893.
def localCycle00224 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 4 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle bfd362374af2bdf0db1c65b8044101b9831a370845ebdeb2d66eadabfa843a76; original global index 14966.
def localCycle00225 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle c02e5aca6ed8b55c780639286c39629d83997fafbe8316cf4852a643cbfcd182; original global index 15002.
def localCycle00226 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 0 4]
    constant := ![-3, 0, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 0 5, .gapLower 5 2, .triangle 34 2, .gapUpper 4 2]

-- Original cycle c0ba258885c2250e08625289fef370ba149b18b8d58cd6914998e7a651c1f545; original global index 15049.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle c166ce68a4dca7ed248f26b9fcdd9d100b58e3c66f466fa1f5f533f7c3d6e46a; original global index 15102.
def localCycle00228 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle c170d1a18ada295017909c83a9d121a29b72500a0a807b1b6a5076119d25b759; original global index 15104.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 24 1, .triangle 14 0, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c2606bebbe346d46f66360e3c9ee272594c3094d1bc8485a7aa0041cffa84159; original global index 15175.
def localCycle00230 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 3, .gapUpper 5 3]

-- Original cycle c29b7a5edc1ee91e558c2df921594e8089915f59ec36480f9fe730bc1d0c8c14; original global index 15190.
def localCycle00231 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 0 6, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 11 2, .gapLower 0 3, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle c344cc63402dd08b9ce79c85f797170fb1b5f492fbe5b151634ba087de89b046; original global index 15234.
def localCycle00232 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c374f607e6edec3b6dea5850b823bde6d69ec72ce0c52b99f3d739555e8fa409; original global index 15253.
def localCycle00233 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 3, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle c5d3cae9a260cead301fa01540a4824690cec8737b4f6c926e334eafcf879375; original global index 15423.
def localCycle00234 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c610d7abf406ec57b70c18a4a4fde3bb3875a887da8cceb95f77ebbb092cc65d; original global index 15448.
def localCycle00235 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .gapLower 0 1]

-- Original cycle c898f191f173dd274d5b26b2aee60252e9d4ecab824bac8fd3ea79662750e449; original global index 15669.
def localCycle00236 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c8fcd33b88dbe5b1254024fd71ffd8668948fb9f20ac9ce5c3eb66c49941f58c; original global index 15696.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle c913315afd8395a5b95dca3362dc46de6c9a93a612d257ba7c988354b9dc54ba; original global index 15705.
def localCycle00238 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c9da6ead821c6cf8fc8ef19faefacf62d401ccd718ecdac47ab5bcd521682119; original global index 15777.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle ca2b8611b356ce53c04cb275e7a1b2bba468a9f6cc847c1b625e5dfc3dfa8957; original global index 15797.
def localCycle00240 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 30 1, .triangle 17 0, .triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cdfda830cda984cbabb49fa48c03544c125e4f3a20ae03bc56fb7380f564315d; original global index 16091.
def localCycle00241 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 0 6, .distance 0 1]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, true, false] }
  origin := ![.gapUpper 1 1, .triangle 4 2, .gapLower 0 1]

-- Original cycle cec9036145d4fc0c31347c3b8821862ff7038757d9132d537919c914881bf6c9; original global index 16141.
def localCycle00242 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .gapLower 6 2, .triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cf05bf874d2375493e8a7bbd30ea9786aed8e6e94d603cfd5f746c5ff767ae5d; original global index 16156.
def localCycle00243 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 6, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .gapLower 0 4, .triangle 8 2, .gapLower 0 2, .corridorLower 0 3, .thetaLower 0]

-- Original cycle cf261df64878600732d54fb8b87697f05b7bbe9df0f54140f15a8fde9c78cccd; original global index 16164.
def localCycle00244 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle cfb5bd7b52835638f9ced2508125dab2dacf30f87458ecfa4b6a93c9738b5560; original global index 16210.
def localCycle00245 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d0b67726b9590116230c3a9515ee13f31d0b9011df3187a1291643d27cf6e5e3; original global index 16287.
def localCycle00246 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 0 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 4, .triangle 8 1, .triangle 29 1, .corridorLower 4 6]

-- Original cycle d26dfdd1db50de8c91698eab4dcccd1c362dc9d0a9956edf8e9e9bbcd68c91e6; original global index 16419.
def localCycle00247 : Cycle where
  length := 4
  data := {
    node := ![.theta 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 0, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d311f04a6e4feb363a87f3ff463d8939a636159fa6c51eaf5f2febd98c2e6c5e; original global index 16464.
def localCycle00248 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d397db57c0359398f6398aa7d3c2f7f8b762c7179b37b263a8f0a6149c5af90c; original global index 16509.
def localCycle00249 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 12 2, .gapLower 0 4, .triangle 5 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle d3ca438ad907f6358603c5bab95f53595d20511a13a1d2901f433a26fa40939a; original global index 16527.
def localCycle00250 : Cycle where
  length := 4
  data := {
    node := ![.theta 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 0, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d4d911c0857339aa494b262a78f6a6caf86045ac64f93ba99d05601db9795d59; original global index 16606.
def localCycle00251 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .triangle 7 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d4f30ac090ea4e2fafd4ced8a2f5c8ee5f197460551c5b9da31dbaf535a797ba; original global index 16615.
def localCycle00252 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 2, .gapLower 0 4, .triangle 7 1, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle d72545ed74e0c078dc7d650e416ec65f1d374f226061c2749f457ae02a6cb0da; original global index 16791.
def localCycle00253 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 34 0, .corridorLower 4 5]

-- Original cycle d8411c6d49dc8b4ba40f75bed0bd58033e72b1dc9b4e440e845b2168e35da628; original global index 16881.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 2, .gapLower 0 4, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle d855f282fdf41e3045733a22e1f5c24e18a716e0b1b37b7c8970a6a00a0a1d34; original global index 16886.
def localCycle00255 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d89657869b889238f76fc8cfbde22fda750b12b0d9a03013bf28a52c033ae950; original global index 16905.
def localCycle00256 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 0 6, .distance 5 6, .distance 4 6, .distance 0 4]
    constant := ![0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 12 2, .gapLower 0 4, .triangle 14 1, .triangle 34 2, .gapUpper 4 2]

-- Original cycle d8e655c92323bfb9cae44ae17e9be59da66451f714f93c07a0996fb43b340cf4; original global index 16935.
def localCycle00257 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d9072c930f8cdeeb972532536a1057d703d388ba44bd5bb329d705b88d454015; original global index 16951.
def localCycle00258 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 2, .triangle 11 1, .gapUpper 3 2]

-- Original cycle dafa6a2fe4e3ee2a34830f3658c2289edbc03360b3235d4da4d3ec50002b1801; original global index 17111.
def localCycle00259 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 14 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle db3f0804d156b4f76ad83c9b1f328a8b49a4483009544675d636369364bebf9c; original global index 17137.
def localCycle00260 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 0 6, .distance 5 6, .distance 4 6, .distance 0 4]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 12 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle dc04151c255f5e963a12de3afbf5188f325eebb29798c219fdea9b7ab1e4e796; original global index 17198.
def localCycle00261 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, true, true] }
  origin := ![.gapLower 0 4, .triangle 14 1, .gapUpper 5 2]

-- Original cycle dc257873c2af2cf0e2882ab9796433415793a720b993385c9e883b49512c3b5d; original global index 17205.
def localCycle00262 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle dcc668307ba434ab2f090713d94fb045571dc40bcab76b3895e85140572789c1; original global index 17251.
def localCycle00263 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, 2, -2, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 18 0]

-- Original cycle dcf0edfb7980cb2ef44543f3daedc28d703780a7432d51155bbec0d40d862205; original global index 17270.
def localCycle00264 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 14 0, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle de09add64b97df467f7d98e176ac826cece27d2912dbfd58022c34ffd62cf88f; original global index 17366.
def localCycle00265 : Cycle where
  length := 9
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 12 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle df4bde941541d549a72c571485ccbc4e7c42c8ed41f2d1c9511729a0b3211679; original global index 17448.
def localCycle00266 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle dfd9ec12b4a20d2b66e8f120eda22a4a3556eb1cd7d0bfeab55f5084c9a45b96; original global index 17494.
def localCycle00267 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 1 2, .distance 2 6, .distance 0 6, .distance 0 5, .distance 0 2]
    constant := ![2, 2, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.gapUpper 2 2, .gapUpper 2 3, .triangle 8 2, .gapLower 0 4, .gapLower 0 3]

-- Original cycle e056b00ea430eb981e8c8579b20eb35893fa7b22154ceb6e8a66009af127c8a4; original global index 17537.
def localCycle00268 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e0e63f04c8243fc901bf267821110113ad5310e6e780fe75c532f8fc851ecd81; original global index 17584.
def localCycle00269 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle e29f0a550b6e829bf60c25bf45f5fe5b48871ac4e0a15fa4a6eca9a6caadee54; original global index 17723.
def localCycle00270 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 13 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e6dbb5fb8bd0463af1c40b8e5d350e6a87c573e381492141cb6262ebf54195b8; original global index 18063.
def localCycle00271 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 4 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e743b5d74cd80a53a91d62e047310312b99c5b5954d365ff07f92fbd3ef6cb56; original global index 18090.
def localCycle00272 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle e833bfe6c89a120309aad9b00047208a58f36fae5722a9b009061e92adae333b; original global index 18152.
def localCycle00273 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true] }
  origin := ![.gapLower 0 6, .triangle 6 1, .triangle 8 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1, .thetaNext 0]

-- Original cycle ea4d1b09e0e56cdb8f6094e44a5331319ad114e1867bf6573a424a1121543a97; original global index 18297.
def localCycle00274 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ea61b3056496b86d70c8d817d2efa9c610d6c7395d6c27d3bec0af3b792fbf83; original global index 18305.
def localCycle00275 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 2, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle ea939180f19d80523579c29e86a2b5abd329c356309e30edf2f5b4ab811658e3; original global index 18322.
def localCycle00276 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .gapLower 0 4, .triangle 5 2, .triangle 11 2, .gapLower 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ecc213ab924a67d5b1b7967756b6f3ca14b3477b2a829502baf156b4c5f8bfed; original global index 18483.
def localCycle00277 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 0 6, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 14 2, .gapLower 0 4, .gapLower 5 1, .corridorLower 4 5]

-- Original cycle ecf6ddb9936bc7d7d7078b04e87c6983a221aeb60d667fc9ea9b1a472a8c22e9; original global index 18497.
def localCycle00278 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle ed203cb8589e1a1de944b8cd44ec43518a0dae0f15fbaf378846f6a4ac22df18; original global index 18513.
def localCycle00279 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .triangle 13 1, .gapLower 6 0]

-- Original cycle edc01128c1b3fbde050beed55e97a04e18f731a88178f97a4a8a87013765f148; original global index 18562.
def localCycle00280 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 6, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .gapLower 0 5, .gapLower 0 4, .gapLower 5 1, .corridorLower 4 5]

-- Original cycle ee105b133c4c9b69ca2c5e59763a9253696191fbe97a85dbbeeb0b83a911a61c; original global index 18585.
def localCycle00281 : Cycle where
  length := 10
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0]
    constant := ![2, 0, -1, -1, -1, 3, 0, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 0 6, .triangle 12 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 0 0, .gapLower 0 0]

-- Original cycle ee4bed3390fae9ea600c14c36613854832ff0b2633ac942d61997e33c9e9256f; original global index 18598.
def localCycle00282 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle ee8dc13a3e98c76c09e03206aeea44c959cbe56e58b68b59c8f2aee260109a94; original global index 18615.
def localCycle00283 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 12 2, .triangle 14 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle f02439739e55ddfb6d6631df6f0996736db7e4cd39a947bc8fa73d3c1bdb2161; original global index 18733.
def localCycle00284 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle f0d0dc4c14e45ca7d7dc23fc10d91cfce5bf254ab51617933277755ead4c9067; original global index 18783.
def localCycle00285 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 0, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .zero]
    constant := ![0, 1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 0, .gapLower 0 6, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaLower 4]

-- Original cycle f14c40b916271c95d300e4f3346cf5c7f12b12a9dcdca2f4cb4519a4abf4edb4; original global index 18815.
def localCycle00286 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 0 3, .distance 0 1]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .gapLower 0 1]

-- Original cycle f1794c33d30ba4184320596e71812a4932842607b532954f500aa6a02caa8094; original global index 18829.
def localCycle00287 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 2 2, .gapLower 0 2, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle f1ffc83c91ca1ea721bc994003d2fb9fff4bf978e7fa35fd4326ad6ee10ee611; original global index 18870.
def localCycle00288 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 2, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 0, .gapLower 1 3, .triangle 21 0, .triangle 11 0, .triangle 1 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle f2fe7f51a079eddcbdf62de11c16c6f0476a8cbd50ebc820e7b2f5d47bce5913; original global index 18943.
def localCycle00289 : Cycle where
  length := 5
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0]
    constant := ![2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.gapLower 0 6, .triangle 6 1, .gapLower 0 2, .triangle 1 1, .corridorLower 0 1]

-- Original cycle f34a043150a8aa57ae5038acb04cdc112568cd2fed22a6c5a2e961b070fb3c81; original global index 18974.
def localCycle00290 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 13 0, .gapLower 0 4, .gapLower 0 3, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f442f66573f0a19b659cbb1bfeddf7075015c093466fa14738de375532c993da; original global index 19046.
def localCycle00291 : Cycle where
  length := 5
  data := {
    node := ![.theta 0, .distance 0 4, .distance 0 2, .distance 0 6, .distance 0 1, .theta 0]
    constant := ![2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.gapLower 0 6, .triangle 6 1, .triangle 8 2, .gapLower 0 1, .corridorLower 0 1]

-- Original cycle f5bdf32346c278fee1e3b19f45c8ec14f5268685f74a46cb0c5faf2dffbf5966; original global index 19168.
def localCycle00292 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .triangle 13 2, .gapLower 0 4, .triangle 7 1, .gapLower 0 2, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f5e629243e486ccc4fe9a96d46c7eddcdfe10d01aec7cf4f9fc82822b6f11c93; original global index 19187.
def localCycle00293 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle f8936e0f3bfc4ff0a78d1b81489867d52914328b406c7c55063035ecc53e2ed8; original global index 19386.
def localCycle00294 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .distance 4 5, .theta 4, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .triangle 34 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle f8ff6805347261315bd8fe541be955420b9eb8443e00a338c88b72f2ea9aaa8a; original global index 19419.
def localCycle00295 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 18 1]

-- Original cycle fa9463c555fca66194b1117504ed97e6e1cc1aaf8dfe9ce900a99aa8ce7786c6; original global index 19548.
def localCycle00296 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 6, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 2 2, .gapLower 0 5, .triangle 10 1, .gapLower 0 2, .triangle 11 1, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle fabee9dd2c37defd41e07b4dc74fb585d271ab97e01dd3b94c357f94fe4997bf; original global index 19563.
def localCycle00297 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 0 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .triangle 1 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fbe2737cac1c77f6006056e535359a3295697452951d62eb540d4cc403bafdad; original global index 19663.
def localCycle00298 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .gapUpper 2 2]

-- Original cycle fcdb830c0b814c3275ae684e9b98f02153906857fb1ab5c81f094cb4498fe0db; original global index 19761.
def localCycle00299 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle feac96aa913b73aa6caa350e5f318a2b50b322e5272517399f4397be3528fdf7; original global index 19910.
def localCycle00300 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 0 0, .gapLower 0 0, .thetaLower 0]

def library : Library := fun id => if id < 150 then (if id < 75 then (if id < 37 then (if id < 18 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 13 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))) else (if id < 15 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))))) else (if id < 27 then (if id < 22 then (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))))) else (if id < 32 then (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))))) else (if id < 56 then (if id < 46 then (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))) else (if id < 51 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))) else (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))))) else (if id < 65 then (if id < 60 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))) else (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))))) else (if id < 70 then (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))) else (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))))) else (if id < 112 then (if id < 93 then (if id < 84 then (if id < 79 then (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))))) else (if id < 88 then (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))) else (if id < 90 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)))))) else (if id < 102 then (if id < 97 then (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))))) else (if id < 107 then (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)))) else (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none))))))) else (if id < 131 then (if id < 121 then (if id < 116 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none))))) else (if id < 126 then (if id < 123 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none)))) else (if id < 128 then (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id = 127 then some localCycle00127 else none)) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none)))))) else (if id < 140 then (if id < 135 then (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))) else (if id < 137 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none))))) else (if id < 145 then (if id < 142 then (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none)))) else (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))))))))) else (if id < 225 then (if id < 187 then (if id < 168 then (if id < 159 then (if id < 154 then (if id < 152 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)) else (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none))) else (if id < 156 then (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none)) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none))))) else (if id < 163 then (if id < 161 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none)) else (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none))) else (if id < 165 then (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)))))) else (if id < 177 then (if id < 172 then (if id < 170 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none))) else (if id < 174 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))))) else (if id < 182 then (if id < 179 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none)) else (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)))) else (if id < 184 then (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none)) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))))))) else (if id < 206 then (if id < 196 then (if id < 191 then (if id < 189 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))) else (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none))))) else (if id < 201 then (if id < 198 then (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none)))) else (if id < 203 then (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)))))) else (if id < 215 then (if id < 210 then (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none))) else (if id < 212 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)) else (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none))))) else (if id < 220 then (if id < 217 then (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)))) else (if id < 222 then (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)))))))) else (if id < 263 then (if id < 244 then (if id < 234 then (if id < 229 then (if id < 227 then (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none)) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none))) else (if id < 231 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none)) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id < 233 then (if id = 232 then some localCycle00232 else none) else (if id = 233 then some localCycle00233 else none))))) else (if id < 239 then (if id < 236 then (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none)) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)))) else (if id < 241 then (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)) else (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)))))) else (if id < 253 then (if id < 248 then (if id < 246 then (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id = 245 then some localCycle00245 else none)) else (if id < 247 then (if id = 246 then some localCycle00246 else none) else (if id = 247 then some localCycle00247 else none))) else (if id < 250 then (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none)) else (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none))))) else (if id < 258 then (if id < 255 then (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id = 254 then some localCycle00254 else none)) else (if id < 256 then (if id = 255 then some localCycle00255 else none) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)))) else (if id < 260 then (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none)) else (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id < 262 then (if id = 261 then some localCycle00261 else none) else (if id = 262 then some localCycle00262 else none))))))) else (if id < 282 then (if id < 272 then (if id < 267 then (if id < 265 then (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none)) else (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none))) else (if id < 269 then (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none)) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id < 271 then (if id = 270 then some localCycle00270 else none) else (if id = 271 then some localCycle00271 else none))))) else (if id < 277 then (if id < 274 then (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none)) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none)))) else (if id < 279 then (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id = 278 then some localCycle00278 else none)) else (if id < 280 then (if id = 279 then some localCycle00279 else none) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id = 281 then some localCycle00281 else none)))))) else (if id < 291 then (if id < 286 then (if id < 284 then (if id < 283 then (if id = 282 then some localCycle00282 else none) else (if id = 283 then some localCycle00283 else none)) else (if id < 285 then (if id = 284 then some localCycle00284 else none) else (if id = 285 then some localCycle00285 else none))) else (if id < 288 then (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id = 287 then some localCycle00287 else none)) else (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none))))) else (if id < 296 then (if id < 293 then (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id = 292 then some localCycle00292 else none)) else (if id < 294 then (if id = 293 then some localCycle00293 else none) else (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id = 295 then some localCycle00295 else none)))) else (if id < 298 then (if id < 297 then (if id = 296 then some localCycle00296 else none) else (if id = 297 then some localCycle00297 else none)) else (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id < 300 then (if id = 299 then some localCycle00299 else none) else (if id = 300 then some localCycle00300 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 3, 6, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 63 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4480)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 63 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4481)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 257 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4482)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 2, 5, 4], ![6, 3, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 94 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4483)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 5, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 2, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 12 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4484)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 5, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 2, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 160 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4485)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 2, 1, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 125 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4486)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 255 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4487)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 6, 5, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 2, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 167 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4488)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 2, 1, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 33 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4489)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 236 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4490)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 5, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 3, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 268 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4491)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 1, 6, 3], ![0, 4, 2, 1, 5, 3]], proof := .tail 268 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4492)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 6, 1, 3], ![0, 4, 2, 5, 1, 3]], proof := .tail 138 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4493)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 1, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 124 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4494)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 1, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 154 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4495)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 1, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 6, 1, 3], ![0, 4, 2, 5, 3, 1]], proof := .tail 117 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4496)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 1, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 124 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4497)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 1, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 154 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4498)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 155 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4499)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 155 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4500)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 139 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4501)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 139 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4502)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 3, 6, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 139 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4503)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 139 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4504)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 139 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4505)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 5, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 27 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4506)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 188 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4507)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 2, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 160 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4508)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 158 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4509)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 3, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 234 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4510)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 3, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 1, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 209 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4511)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 5, 6, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 58 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4512)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 138 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4513)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 5, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 148 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4514)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 85 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4515)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 2, 3, 1], ![0, 5, 4, 2, 3, 1]], proof := .tail 24 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4516)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 0, 4, 2, 3, 1]], proof := .tail 227 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4517)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 218 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4518)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 218 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4519)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 5, 1, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 4, 2, 3, 0, 1]], proof := .tail 6 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4520)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 5, 3, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 5, 1, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 3, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 40 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4521)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![66, 235, 173, 70, 157, 165, 56, 286, 8, 71, 30, 11, 11, 123, 286, 286, 286, 286, 192, 69, 54, 195, 290, 98, 92, 251, 61, 205]) }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4522)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 275 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4523)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 152 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4524)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 166 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4525)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 219 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4526)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 100 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4527)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 172 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4528)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 181 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4529)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .tail 239 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4530)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 1, 2, 3]], proof := .tail 83 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4531)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 266 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4532)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 225 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4533)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .low6 (![68, 50, 89, 183, 136, 196, 128, 77, 279, 169, 115, 122, 248, 272, 113, 228, 146, 248, 245, 62, 282, 248, 274, 43, 198, 263, 240, 65]) }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4534)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 2, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 112 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4535)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 1, 6, 2, 3], ![4, 0, 1, 5, 2, 3]], proof := .low0 (![164, 235, 173, 134, 277, 193, 52, 286, 287, 142, 252, 88, 300, 118, 286, 286, 286, 286, 217, 292, 29, 289, 267, 177, 177, 88, 254, 87]) }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4536)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 1, 2, 3]], proof := .twoLow (![some 168, some 235, some 173, some 264, some 55, some 193, some 86, some 286, some 186, some 144, some 78, some 88, none, some 130, some 286, some 286, some 286, some 286, some 297, some 49, some 88, some 289, some 47, some 95, some 95, some 280, some 254, some 87]) (![some 143, some 50, some 104, some 230, some 295, some 2, some 163, some 224, some 103, some 44, some 161, some 79, none, some 185, some 53, some 38, some 79, some 259, some 270, some 207, some 79, some 242, some 76, some 79, some 39, some 59, some 229, some 79]) (fun p0 p6 => if p0 = 12 ∧ p6 = 12 then 151 else (0)) }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4537)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 1, 2, 3]], proof := .twoLow (![some 168, some 235, some 173, some 107, some 261, some 226, some 265, some 286, some 186, none, some 215, some 81, some 281, some 130, some 286, some 256, some 81, some 286, some 73, some 215, some 81, some 82, some 110, some 81, some 99, some 81, some 201, some 81]) (![some 141, some 31, some 278, some 17, some 295, some 2, some 163, some 175, some 16, some 101, some 156, some 79, none, some 260, some 25, some 25, some 79, some 25, some 129, some 253, some 79, some 84, some 244, some 79, some 233, some 59, some 294, some 79]) (fun p0 p6 => if p0 = 9 ∧ p6 = 12 then 231 else (0)) }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4538)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 1, 2, 3]], proof := .twoLow (![some 168, some 235, some 173, some 107, some 108, some 105, some 285, some 286, some 186, none, none, some 176, some 1, some 130, some 286, some 286, some 286, some 286, some 73, some 93, some 176, some 82, some 110, some 22, some 99, some 204, some 34, some 67]) (![some 90, some 250, some 283, some 132, some 295, some 2, some 163, some 271, some 179, some 145, some 26, some 79, some 32, some 45, some 206, some 75, some 79, some 247, some 262, some 127, some 79, none, some 199, some 79, some 203, some 59, some 191, some 79]) (fun p0 p6 => if p0 = 9 ∧ p6 = 21 then 211 else (if p0 = 10 ∧ p6 = 21 then 159 else (0))) }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4539)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 2, 1, 3]], proof := .tail 137 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4540)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 2, 1, 3]], proof := .tail 137 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4541)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 232 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4542)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 1, 2, 3], ![4, 0, 5, 2, 3, 1]], proof := .tail 293 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4543)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 0, 2, 3, 1]], proof := .tail 293 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4544)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 4 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4545)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 3, 6, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 2, 0, 1, 3]], proof := .tail 190 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4546)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 2, 0, 3, 1]], proof := .tail 293 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4547)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 2, 3, 0, 1]], proof := .tail 80 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4548)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![6, 3, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 1, 2, 3], ![4, 5, 3, 2, 0, 1]], proof := .tail 237 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4549)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 3, 6, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 2, 0, 1, 3]], proof := .low6 (![210, 178, 42, 298, 246, 153, 163, 140, 216, 214, 116, 116, 116, 36, 46, 102, 221, 221, 97, 0, 96, 96, 119, 111, 21, 162, 35, 135]) }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4550)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 2, 0, 3, 1]], proof := .low0 (![114, 7, 19, 147, 5, 105, 273, 208, 171, 184, 288, 176, 133, 72, 3, 3, 3, 3, 37, 243, 182, 23, 51, 202, 64, 13, 48, 197]) }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4551)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![3, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 2, 3, 0, 1]], proof := .low0 (![168, 241, 258, 14, 220, 105, 194, 120, 150, 60, 106, 176, 222, 200, 60, 276, 187, 291, 60, 189, 296, 41, 212, 60, 60, 170, 249, 223]) }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4552)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 2, 5, 4], ![6, 3, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 1, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 121 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4553)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 5, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 2, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 9 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4554)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 2, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 109 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4555)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 2, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 167 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4556)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 2, 1, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 57 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4557)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 2, 1, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 15 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4558)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 131 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4559)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 213 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4560)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 284 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4561)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![0, 4, 2, 1, 5, 3]], proof := .tail 284 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4562)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 6, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![0, 4, 2, 5, 1, 3]], proof := .tail 138 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4563)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 124 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4564)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 3, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![0, 4, 2, 5, 3, 1]], proof := .tail 117 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4565)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 124 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4566)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 131 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4567)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 5, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![4, 0, 1, 2, 5, 3]], proof := .tail 213 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4568)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 5, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 149 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4569)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 5, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![4, 0, 2, 1, 5, 3]], proof := .tail 149 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4570)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 6, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 1, 3]], proof := .tail 138 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4571)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 1, 3]], proof := .tail 124 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4572)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 1, 3]], proof := .tail 124 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4573)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 3, 6, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 155 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4574)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 3, 5, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![4, 0, 2, 5, 3, 1]], proof := .tail 117 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4575)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![4, 0, 5, 2, 3, 1]], proof := .tail 124 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4576)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 0, 2, 3, 1]], proof := .tail 124 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4577)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 155 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4578)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 3, 6, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 2, 0, 1, 3]], proof := .tail 20 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4579)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 2, 0, 3, 1]], proof := .tail 20 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4580)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 2, 3, 0, 1]], proof := .tail 20 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4581)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 1, 5, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 1, 3], ![4, 5, 3, 2, 0, 1]], proof := .tail 91 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4582)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 3, 6, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 1, 6, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 126 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4583)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 126 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4584)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 126 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4585)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 3, 5, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 1, 5, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 27 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4586)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 174 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4587)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 4, 6], ![2, 0, 5, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 2, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 160 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4588)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![3, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 10 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4589)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 3, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 28 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4590)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 3, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 284 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4591)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 5, 6, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 299 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4592)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 138 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4593)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 148 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4594)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 2, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 85 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4595)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 5, 3, 2, 6, 4], ![3, 0, 5, 1, 6, 4], ![2, 0, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 1, 2, 3, 5]], proof := .tail 28 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4596)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 5, 3, 6, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 1, 6, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 1, 3, 5]], proof := .tail 74 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4597)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 5, 6, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 5]], proof := .tail 238 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4598)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 5, 6, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 3, 6, 1], ![4, 0, 2, 3, 5, 1]], proof := .tail 138 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4599)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 0, 5, 6, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 2, 6, 3, 1], ![4, 0, 2, 5, 3, 1]], proof := .tail 148 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4600)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 3, 2, 5, 6, 4], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 0, 6, 2, 3, 1], ![4, 0, 5, 2, 3, 1]], proof := .tail 85 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4601)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 0, 2, 3, 1]], proof := .tail 85 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4602)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 3, 2, 6, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 0, 6, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 0, 2, 3, 1]], proof := .tail 227 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4603)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 2, 0, 3, 1]], proof := .tail 180 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4604)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 6, 0, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 2, 3, 0, 1]], proof := .tail 180 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4605)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 3, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![6, 3, 0, 5, 1, 4], ![6, 2, 0, 5, 1, 4], ![5, 6, 0, 1, 2, 3], ![4, 6, 0, 2, 3, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 18 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4606)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 3, 6, 2, 5, 4], ![0, 6, 5, 3, 2, 4], ![3, 6, 0, 5, 1, 4], ![2, 0, 6, 5, 1, 4], ![6, 5, 0, 1, 2, 3], ![6, 4, 0, 2, 3, 1], ![5, 4, 2, 0, 3, 1]], proof := .tail 269 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4607)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (4480 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 4480 ≤ id.val) (hhigh : id.val < 4608) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 4480)) = true := by
  let j : Fin 128 := ⟨id.val - 4480, by omega⟩
  have hsum : 4480 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (4480 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard035
