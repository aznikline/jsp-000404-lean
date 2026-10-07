import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard024
open N4R2RowDataReplay

-- Original cycle 00628488d555dc65caf8f1bb03f782c0a85ffa3827deaef004557eee4b6e5642; original global index 34.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 23 2, .gapLower 6 3, .triangle 8 2, .triangle 11 1, .gapLower 6 0]

-- Original cycle 013fb81c50198c824249f97487116345755b8793a66e93a1ce58cfa6c38194e6; original global index 107.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 017ac7c1acbd676601f197c9fdfbf2ff095877de8d3fefc4f3b9ee8abc45d843; original global index 122.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 2, .triangle 9 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 01f89db81b07e4eda81b8d62078cb6863271555ca8d3756887acb6ee18764d3d; original global index 155.
def localCycle00003 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 02cc755b8d5c481333ab490ccd2e5063671390358db20c78efbf1ed0160ebf22; original global index 220.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 05f0f40e0f2d305259dd5bfce513204bb7a89f56bb198bf0dcd08196932b3eac; original global index 491.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 0ab8c722cf8c87e6ee5b8e5a7a6ea8fcb069fa485a6f37efdc14119fe9c6d881; original global index 853.
def localCycle00006 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0b39f52b677d7305e900831e40b6993bc8c9116cca9e262a77f04df5eb43aa59; original global index 899.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 0ca791d4b99de8d5c2dd8cf392ddc9a22f9b0661acce7588c244cb8239f273b7; original global index 1000.
def localCycle00008 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 5, .distance 5 6, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 2, .triangle 10 0, .triangle 33 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 0e197887aa3397d0a16d63d85f0a5aa2417be55ec5724f5627806d6db1974337; original global index 1112.
def localCycle00009 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 0f13a09f327697455702fbc3c6eb5b2512bddb4114f25b550bdb7c314c1db475; original global index 1197.
def localCycle00010 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .theta 6, .theta 5, .distance 4 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -2, 0, 3, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 22 2, .triangle 24 2, .gapLower 6 4, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 106b818db01f92421483719b258efe546ad9a83f04d4d114528d8c7d9010ee33; original global index 1318.
def localCycle00011 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 1 4]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 23 1]

-- Original cycle 10ac8957cc4b0a88f1d8e22b1357fe0060338bc8edefe2a5f041116a710398ac; original global index 1337.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .triangle 29 1, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 14ca9bf6f3ddaefc473e75a2bc4492620c37092bb9d00342cb5ab5cab5600f01; original global index 1650.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .gapLower 6 2, .triangle 11 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 15a88fec83e2000cc44e0057384ee17a542989c079d9c75bfe1f7a25a1d1afa1; original global index 1719.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 1a8838625cbe8011e224979405c9ee9a6217e46965093780dbe83cbb96af0970; original global index 2067.
def localCycle00015 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 1c72fd9170f90623e5771f9d7dee06f71355da6ee87f3086d6a97c3ee01b1ac4; original global index 2183.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 2, .triangle 18 1, .gapLower 6 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 208169fb42b5d44a668cdc782dbad63fcd8c6e3e487134eff5eaceecec4d328e; original global index 2494.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 212630bda01fc9b1369e9bcda09fde8c74d82015b7b7581e8060758f798cbf3b; original global index 2540.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 245447a1413570f8e859257463c11eb23b22e35bd9dc69158fc67a869eb27ab0; original global index 2784.
def localCycle00019 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 24 1, .triangle 34 0, .triangle 28 0, .triangle 6 0, .triangle 0 1]

-- Original cycle 24f7ff89966067ea7c20779110ae4afab20c765b258dee66c36a138296a9b621; original global index 2834.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 29edc2f6d5d5648da1e772e1b878b1bfba48fa5b60f7444afec461b1d0bccbc6; original global index 3199.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 2adc227e99e1e2c3c793ba0699285037ec97c2b35dafe254865cc8e97ed67cf6; original global index 3267.
def localCycle00022 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 11 2, .triangle 13 1, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 2ccfd431eec86a680d580398642fee210538513dd1211d49ab4d7b0f9dc49262; original global index 3422.
def localCycle00023 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2d2ec0c0ee908ff21b0e2262ee7354542259a2b3ab60894e8f61abcdc557ecd5; original global index 3448.
def localCycle00024 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .corridorLower 2 6]

-- Original cycle 2de94d94daeecf2d21456d676ebb17bba990389220e4bbdb16501fe87cc39a82; original global index 3506.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5, .zero]
    constant := ![0, 3, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaLower 5]

-- Original cycle 3249e7fad32bb8ba47394b43628dba4ea689f9b22bfe0c23f838742209b83414; original global index 3839.
def localCycle00026 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 2 6]

-- Original cycle 334dfe0b94780b002de1ecbf7795f1dba2359c93d2081a79214c9f5425d63fb3; original global index 3926.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 2, .gapLower 6 2, .gapLower 6 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 359bee572cc632172fc810db581ff4a81fa54bbc475fa3bf5d89f177ce3b41da; original global index 4107.
def localCycle00028 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .corridorLower 3 6]

-- Original cycle 36c4321d170dbd78a7818f9e749dedcc3c8287a60283f56af79d34590f3ef81d; original global index 4209.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 386bbb91930c1a58ec4ae9883701595b45e727c24bf5cde44eb43ca2d3536a84; original global index 4339.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 386e10055294ac395f18e70a6d112e0b8aa66b7fdfa12bad10e0ae13bf6a09d9; original global index 4340.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -2, 2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .gapLower 6 0, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 16 1, .corridorLower 2 4]

-- Original cycle 390e7de2ac19ce1ebdb3a5556d14220e21f35b7b3729673447bd950441a09294; original global index 4389.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 393f5dce4c35096d60baa06bd8dfa71374b39ca36f6518231c17a82160d4651c; original global index 4404.
def localCycle00033 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 4 6, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 34 1]

-- Original cycle 3ba43fdbcc18474355068155b5d5ee8b4dbcc75af7cd87ea5ff6ef0d5ed2e49f; original global index 4610.
def localCycle00034 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 3dd1832b52ba278009b6c3a04cc8d954a551965feb47903fbabe6c9d05482b2a; original global index 4784.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 5 6, .distance 1 5, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 1, .triangle 24 0, .triangle 17 1, .triangle 28 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 3e55139de6387254a2129ab5b893f4616fedcf418b2c3f7002489181eaf5e0dd; original global index 4824.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 3eff64aebcf4fa6b1bfe4109d895c5c38bb9919533e1875aa4061ab9b7b96176; original global index 4871.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 7 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 403ecae26e33a129517bd942b58e5fc2c5e1337e7b8cf312e7c86a3e87c8dc69; original global index 4958.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 40f50e66518464a307b924ad07ef01d53643b6718c030c8811adb22f1529879a; original global index 5017.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -2, 3, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, -1, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .gapLower 6 0, .corridorUpper 5 6, .gapLower 6 5, .gapUpper 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 420de4cf93985dfc6930d75173bad97fc735a8e8ecce84ef02950a21a4b91729; original global index 5089.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 42e0dbb5f79e42e0c3d791d8f1dbcab1fc47416005a813b4bc115fde718a016c; original global index 5147.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 18 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 46b1d1067e87f893b6efef8080aaaa96e527f99e1de56891fed4f73bd0a38cf0; original global index 5474.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 0, .triangle 17 0, .triangle 28 1, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 4a100ab4bc2877af71309713d91416fa5c134bf4e0387f8bfc6fe4d9ea3289d1; original global index 5750.
def localCycle00043 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 4af92d91cf521bd725b9354c6228656c50fcdf7f2761a3df639f9dd23d6730fe; original global index 5818.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .triangle 8 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4c60e5249d5ab04fdaa9815bdfe80bde1c508b1cb0708d2117c6e4143d318106; original global index 5931.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 24 1, .triangle 30 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 4d72eaf9510a51e32cd6a0243718a6465b3b29a1d1bfcf18a7bcf041b696f74b; original global index 6012.
def localCycle00046 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4dccf1a53b31a773bf439f897216d24971fc93f62daef9da1f705b5f8e285ad2; original global index 6041.
def localCycle00047 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .gapLower 4 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 4fb7f548143269734e6238a0259873d8fc74f7cfbb17aac7ba28d8567aa62331; original global index 6191.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 52836fc89deece694ece217733bdee36fc269d77b767ba206b959e49b3929682; original global index 6414.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 0, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 54f2792d3deb7be1627d652d0afe20261e2fe3a5509b281b9b13d3d46c7e1502; original global index 6575.
def localCycle00050 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 0 6, .distance 0 2, .theta 2]
    constant := ![3, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .gapLower 6 2, .triangle 8 1, .gapLower 2 0]

-- Original cycle 55434800f1e1183d8f4b3a65fdab93e80357f4c19bf65d6132bc34532fca963a; original global index 6600.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 55ad9786b3edc069bf35c4509a39fafb07f8394acf42ae44f0ce94dd1aae3733; original global index 6646.
def localCycle00052 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 594b1d628e30eb07b9b46d55da3ac364d1e8b1c93e3a214948f893910f834e74; original global index 6929.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 5a44bf134757bd85e0d0a4f53e2461d511431a13bc7a91aa346f0a99418bfdea; original global index 7023.
def localCycle00054 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .theta 4, .zero]
    constant := ![0, 2, -2, -2, 0]
    coefficient := ![1, 1, 0, -1, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .gapUpper 4 6, .thetaLower 4]

-- Original cycle 5bc5d2574442e515d33d41fc1471a6b02730d9894e6e52a7fbb59cde3c2d322b; original global index 7132.
def localCycle00055 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 5e610ff667a512923b3cdc207954348272abe28e4a1f211ddf7e127198d1d4be; original global index 7342.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 24 0, .triangle 30 2, .gapLower 6 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6051a4eff7e5225fb53998534e7172ce57c7d610698af8d1a9bd9185bf85d86f; original global index 7500.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6475d2fef7ca4bb9f212e665419a2835cc9223ea45e00bc200fd726689c927f7; original global index 7824.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 2, .gapLower 6 2, .triangle 11 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 67335d407e25d404fc8d983c9f88f5df36d66f094e37cffa7a5525acbb9bd1d1; original global index 8022.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 67c50ccc0cf08ab2b02fe817ed3e745b568da76300efc4b97293353ca6c47d98; original global index 8061.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .triangle 8 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle 688c87f4b4cf2d121a1ea0705c2657c509c0d96c41dd51467b2630fa5bd9394b; original global index 8132.
def localCycle00061 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2, .thetaLower 2]

-- Original cycle 6bdfe14dfe50e88c4fcf5655eccde729feac88a4d48e6fe023602ed7b5f593d6; original global index 8403.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .gapLower 1 4, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 11 0, .corridorLower 3 6]

-- Original cycle 6d94d7ed42c671efff4a7118a50661a95ddc2af356b8e32c6750dbabed69cca9; original global index 8517.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 6f686c346a18a379ecd1c73113ec1c4209eaf74e12b30d3baf5d77d3be3998ff; original global index 8636.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 2, .triangle 11 0, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 72ab011ff27d0aa989699736554d26c859027362166a46f2991e7dad84a4ae5f; original global index 8878.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2]

-- Original cycle 72cb81ba8e7c5d3f164b514dc2144e7b3771c25c29561d5e27203ebb327a0ed0; original global index 8891.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 73cff67f1ce2fc038d6b71d9563e9fdf157862a7661d6d84510bc88827c7e293; original global index 8979.
def localCycle00067 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 2 6, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 3, .gapLower 6 3, .triangle 30 1]

-- Original cycle 76313ab807a157169a62bc59d3ad9da6219656494a9d8e7d7959bcbea02abe01; original global index 9149.
def localCycle00068 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 11 0, .corridorLower 3 6]

-- Original cycle 76a43cfc37fd263d850ad45645dad09b41c6f3db346fcc124c8b296d8b37d19c; original global index 9181.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 77de1722ab106f5ba85b9bbf80543bce463e6ced52b0c343b549e4e5ae8e206b; original global index 9269.
def localCycle00070 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7928a56c4567a5baac9c97ef7a01dbb513593b334c30d4eb1f64a4c64322c8b0; original global index 9377.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7a5ba415507fed13fabaff4a27daf151d1da88d0c208c97f77e7209b936ab8be; original global index 9465.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle 7bff02fb74e5516c6e2c4cfb788c59a5068a233f5bf2f3435482c88fc06e0717; original global index 9590.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 7c01d5e7cff057edde99a1c7de46c6174b66855588bd066ac3ff59be24b29eba; original global index 9594.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 7c2e657ea4c3f82b8b0d7a7ee6c1ef1f06debcd31473ab45c104f257bddcbe53; original global index 9609.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 7e176c7d19f5671a0631f5bb48cb45f36b0092682b1142c8c7dfefb94b7caa6e; original global index 9795.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 6 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 82253b5cde89ec0b76b5464917cf3170d57d7a894c8345607299b8ee784d42cc; original global index 10107.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 4, .triangle 30 0, .triangle 28 1, .triangle 6 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 8555d114645f944ed5d514537d5f80dd98332a75d5b760ddef51a26940adbf23; original global index 10344.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 12 2, .triangle 14 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 88592f8f929e6d30e93f40d5adc21ed78da905d97a2fb7c0fb041fa00df9638e; original global index 10566.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 24 0, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 89df97c038abebef38738ec32a5c09908784fabc4216c93d81d9e9f44e25cef9; original global index 10682.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 8a89a97a51beb062890cb94daa205184d1eb00dc59a0a10ec636bba31961b5c6; original global index 10731.
def localCycle00081 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle 8d960cf6f2d692642218765544a81ddb3c5b36884b1eaafd996723ac6313c1de; original global index 10948.
def localCycle00082 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 916cbbc649c1de46d91caf84d531d976c2e04b9b2786e28238a36edb95b394bf; original global index 11264.
def localCycle00083 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 6]
    constant := ![3, 0, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 4 2, .triangle 11 1, .gapLower 6 0]

-- Original cycle 91c43a471cc013d296daeb64220554b1eed16a2e8640e0c1d2b654990ea85768; original global index 11298.
def localCycle00084 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 944c5b0f62a077b06c49e369b1d00c512f6e27fe34241ee415edd48a912fed6f; original global index 11505.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 0, .triangle 31 0, .gapLower 3 2, .triangle 11 0, .gapLower 3 0]

-- Original cycle 953fd9549b60be534bfc73c117510729ba457dc16223b93c7f39ac733def1924; original global index 11595.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 99f0712265414459d764bb692d3768b95db855e9c76fd890591ab26e413a53c7; original global index 11948.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 24 1, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 9b05da975bd2ca349f8cd3c9cb1461f0db6009ba368b729a0c8c9694e5aa4fa1; original global index 12048.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 2, .gapLower 6 3, .triangle 8 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9be251bebf69eab9005c7632e0f84b6d2302b928e69f29c555556d526f4ecb56; original global index 12125.
def localCycle00089 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 0, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 9f4768491eda5ed1e6c39bb37637f242314f6cc7cbe8c91b0c7271f0f01b8497; original global index 12399.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .corridorLower 3 6, .thetaNext 2]

-- Original cycle a63607a3ac0bb589100c154e21a86d5ff934f66c24749d6f447391615dc50b78; original global index 12912.
def localCycle00091 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle a7db437f962937988c19f43e7d873bb40b797c8f51061877a1ecfa4054a04318; original global index 13066.
def localCycle00092 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 1 1, .triangle 22 1, .triangle 28 0, .triangle 6 0, .triangle 0 1]

-- Original cycle a8da0b48740f62cb57039732ffc77dbb9c2cf95882f4f5c567a2292bb4319607; original global index 13142.
def localCycle00093 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 4]
    constant := ![2, -2, -2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 30 0, .gapLower 2 2, .gapUpper 4 3]

-- Original cycle a8de35ee4192120725974ee49779bb0f07c07d40fecdb49e8d6e25376ba830d8; original global index 13145.
def localCycle00094 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 0 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 13 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle a9b33030286cdfc6f0153fbe6fe23dcada307c8cdc8fb4f4488d70023b48d47e; original global index 13210.
def localCycle00095 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 22 0, .triangle 2 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle aa536b7c1d1cd53107e38d3a51c0001f4c5ce8b08eaf8beb97d7a7ea7e9119f8; original global index 13263.
def localCycle00096 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ab83af34078b7d2f5421e4e4ecf335795cea26aabe9dd2e8c2c707ac805e8766; original global index 13362.
def localCycle00097 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 2, .triangle 8 2, .gapLower 6 1, .triangle 33 1, .triangle 31 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ac5c1eb93766e84a7f378298f0c5ac875cf8fffe3eeb9bbb3f1575836008425e; original global index 13437.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 3, .triangle 30 1, .triangle 28 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle acffb5baa0af26fb1c9bcb945e6e8e30ac0353d7beb5fafc9cd184c32a4849f4; original global index 13484.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 9 0, .triangle 11 0, .corridorLower 3 6]

-- Original cycle ae6ea0f74b2ec15ab084282e0f0209274d507a9c6791885af8a9feae46f0be08; original global index 13614.
def localCycle00100 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .theta 2]
    constant := ![3, 0, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .gapLower 6 3, .corridorLower 2 6]

-- Original cycle b0c387b4a915f716a6104678e9fb873c2c6faae8fb2c335ee213dd85806209d7; original global index 13804.
def localCycle00101 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle b1207e54747da4ba93036e2c6fbf987a5c4f3f83851787472ec01e39f42d9856; original global index 13832.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 23 2, .gapLower 6 3, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle b168bd7f09351ac7e0bf9651dd8d41ac7fb661e567104552ba21958bb0ff5130; original global index 13862.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b1ba3de5aa0a2151b5c85b24dff13f164516440f8d35992aa902cbfb4ef1a8ca; original global index 13887.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle b21a5ef5de41ec9782ef2e755e5a927af7df2cc1103a7f4a256ba006cb3c86d9; original global index 13917.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 21 0, .triangle 27 0, .triangle 5 2, .triangle 9 2, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b46b63231d16c176516541c2e48a6990f028283434080622d9d757d1bf0acde9; original global index 14095.
def localCycle00106 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .corridorLower 3 6]

-- Original cycle b4c6cb0e5aa98f9dbc0791a19b7be2c5881d6bfa99c1d513f77e805ba3636f57; original global index 14115.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle b5419bdd2ad315fdf09a1b3688802cc41927bb45953433ba0bf58375aae61431; original global index 14162.
def localCycle00108 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle b97880edba80d04aba6699b84010a8efdf28795aa4a79124248411535f0798fb; original global index 14473.
def localCycle00109 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 25 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle bb93b6e66ca1e5fab2b56863cd6540b6ce3e0a1903e256d761659bee8c11a43e; original global index 14643.
def localCycle00110 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .gapLower 3 3, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle c2c680af3a3255896650afc4fc1666e6a4579991f5f927e419c35c955bddceb5; original global index 15199.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 2, .triangle 9 0, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle c2e6aca958a3169557f548f7ee2ba836e8fa8d5040455a437eb61eadc131180a; original global index 15209.
def localCycle00112 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 23 1]

-- Original cycle c5f8596581567634dd9a10adfd4cbc53e6325f9b3885f82239db7ceb8852178c; original global index 15439.
def localCycle00113 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 9 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle c69ca00d0b0005ab84fe9565e7cd1826408d0411ab12e4b6752e86983112beb4; original global index 15494.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .gapLower 6 2, .gapLower 6 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c7c720a3d5600a8bb542a5c53556cc704a0a173c492c523b8bd41ef6b1bfa47a; original global index 15600.
def localCycle00115 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 0 3, .distance 0 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .gapLower 1 4, .gapLower 3 2, .triangle 5 1, .triangle 8 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle c8ea02a498655b0743dff5bbae2a2fb421b9a5ef7a14afda7f428510bcd6355a; original global index 15691.
def localCycle00116 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 1 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 2, .gapLower 6 4, .triangle 30 2, .gapLower 6 2, .triangle 11 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle c97abf0237be4276831a4b90f40ca1ffbbcb061b6d140a243ef35fffeabfd7a6; original global index 15752.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 0, .triangle 33 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle c9eff2f17bd378cc405d47e2cc854c75acf717da932767ffdec8566c2a872b8a; original global index 15781.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle cbbb3ee91a70b2c12805acd38ab885f3c75b66f689f74aa53ff5f65413626d7e; original global index 15917.
def localCycle00119 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 0, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cf44fd2872ed7540eed3efe566bb89e2608ed9c30f36c0f9994b20cffca92acd; original global index 16176.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 0, .triangle 28 0, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d251bd4106d41d0029e9107b668de27e9113741e5ff7e33eb32991d761dde346; original global index 16409.
def localCycle00121 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 0, .triangle 15 0, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle d25bbc02d68cdd9e187b881fbf152f88d8b1e55b6a86f7b3eaf3ab7b89a96ce2; original global index 16415.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 3, .triangle 30 1, .triangle 28 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d26ebd5468ca0eb1ade94f33badc38b4dc8d85e9c59f220e786570e6b631e70b; original global index 16421.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .gapLower 6 3, .gapLower 6 2, .triangle 11 1, .triangle 32 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d33db5f3f4b727344de65bcf56af875e74da6dd79c3a6c11087c3ededd55bc90; original global index 16478.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d4ee9de74fdf2160721c207fbed163245652bf670b1a17a8e51b97f1cc4b0122; original global index 16613.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 4, .triangle 22 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d61b56a84279dd5b14ee2afb6e823487cf9665824ba386dbef441b755146912f; original global index 16712.
def localCycle00126 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 25 2, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle d6944e0bc398f503101cb941024af5d59f498a1450d0a852a22d41e8008d6948; original global index 16751.
def localCycle00127 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 30 1, .triangle 28 1, .triangle 6 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d7eb25b6e383656623fa86d2d90ce112f17b33eacb45706ced792e2767732a66; original global index 16847.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 0, .triangle 24 2, .gapLower 6 3, .triangle 8 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle db04932508dfdac08f5436ba4424e421f604095797dfbe6aa4436ba999b08f1f; original global index 17115.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -1, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 22 2, .triangle 24 0, .gapLower 6 3, .triangle 8 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle db168df628913ca6329db55dab8ad0042d9332ab27ac1406f9e5bc18cd917f6a; original global index 17121.
def localCycle00130 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 4 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle dcb6336aa7ce0e4b55be5898e0a382dc8d4d9bd05760462859b666e4436cd193; original global index 17243.
def localCycle00131 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle dce2becb9e5415d0398c67b7869a0bf279800fcdaf0238f235e56aeed67c7e59; original global index 17264.
def localCycle00132 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 29 2, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle dea9ad4d7d4a77ec3c1ea093a145a140ea716c63fcad82022b3b01b043b0ab42; original global index 17410.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle deffebc21e14659f801ed5841d0d514ed4dad75608c447bb8f568cb1fd0a6b97; original global index 17433.
def localCycle00134 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 0 2, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle e0e9ab00adbea85b67e5166c7bb8224cd0caa7fdca2402043dfdbee9adff89f8; original global index 17587.
def localCycle00135 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 2 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 18 1, .gapLower 6 2, .corridorLower 0 6, .thetaLower 0]

-- Original cycle e19af98c647957f372b0f3b01ada70ead585a0bece4747dfa4058e2dab61fe64; original global index 17641.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 5, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 26 2, .triangle 28 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e3952b2a11a0af34c81dd4acae7aec0d20710bab0ee48afb3f83f01e33a8eec5; original global index 17797.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle e3bb372fcaef8247878717490c8f26bc94ed1f985ca2a550f0d269b1906481de; original global index 17808.
def localCycle00138 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 4, .gapLower 6 4, .triangle 24 1]

-- Original cycle e3c28b44f5741d51139dbd63858dc05e95b72a50a3e46e12b2031e7b496362b6; original global index 17819.
def localCycle00139 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Original cycle eadc041b1a2653ff54165f713c601836ca7085241cec3a33fe1651314c626a68; original global index 18345.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle eb12017d445b2197eebf02fe0dfe8db8d973d4318708e40d9350e641e107c66a; original global index 18357.
def localCycle00141 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle ec105a3befe47335b4d75eacd97b18fe422a0f3bf40ca87db57bf38433dd8d64; original global index 18425.
def localCycle00142 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 4, .gapUpper 5 4]

-- Original cycle ee99bd7e7d7f75c43c05bd6fa5a30aba504b9707e4a82f800b035ede6b774881; original global index 18620.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 29 0, .gapLower 4 3, .triangle 9 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f24bffcaa8348e3bcf442de8144966e787b9fe1311f0d8af9cb8526ad53acea2; original global index 18895.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 5, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 2, .theta 2]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 20 2, .triangle 24 0, .triangle 30 2, .gapLower 6 2, .triangle 8 1, .gapLower 2 0]

-- Original cycle f31ad6595733adb9e866f7a090096996fc3e383577428584a00bf1a1825e00eb; original global index 18951.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 22 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle f36102a888ab63a6642c6c8fdffe15167f65d463c70edb1a59254cbaa053d27a; original global index 18983.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 0 6, .distance 3 6, .theta 6, .theta 5, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .gapLower 6 2, .triangle 11 1, .gapLower 6 0, .thetaNext 5, .thetaLower 5]

-- Original cycle f65a2bbe18b13c626b9d9c5697b8683d7cdc3ce1196779d38da49f3ee4d6b244; original global index 19214.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 19 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle f71a4a88a25fa72ff2939c92dabfeaca9f6145eef38dff9814e4a38c8a83e2fe; original global index 19271.
def localCycle00148 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 29 0, .gapLower 4 3, .triangle 12 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f7f29a369225a3feea9818ecbda1377e620ea314b410d89c07b3ef520813679f; original global index 19329.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle f934225e346eca5e917a70a8a80a53d5dee9739da2822183c92d164f0141f970; original global index 19436.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle f99458bd340cdf790e5fe4d641731b834d6c64642a9591f65624c455bc39f806; original global index 19455.
def localCycle00151 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f9eb6f7b0cf9f43cdc6b7829d8fd7d822377e4d503cedfa9544ecda08d9505c5; original global index 19489.
def localCycle00152 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 24 0, .gapLower 1 2]

-- Original cycle fa12f4cdefe43568b9d82fe98e71af72279cddba7955cf13db56c25a1b15ca03; original global index 19498.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 0 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 9 0, .triangle 11 0, .corridorLower 3 6]

-- Original cycle fa9d1877970e2e19e1a5c66cf5e8d102effffedbf098db62938a3ae6eef5594e; original global index 19553.
def localCycle00154 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 20 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle fad4182ee5f36e948dc3e4ce126fbfab7e95e2c251eb0f287608bd6803e09ee5; original global index 19570.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 3, -1, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 3 6, .thetaLower 3]

-- Original cycle fb7048409d2ce4ee58ee197e999a751a90902a1405191d68e827bf0f472f2d8a; original global index 19628.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 0, .gapLower 3 3, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

def library : Library := fun id => if id < 78 then (if id < 39 then (if id < 19 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 14 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)))) else (if id < 16 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)))))) else (if id < 29 then (if id < 24 then (if id < 21 then (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))))) else (if id < 34 then (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))))))) else (if id < 58 then (if id < 48 then (if id < 43 then (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))) else (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))))) else (if id < 53 then (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)))) else (if id < 55 then (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)))))) else (if id < 68 then (if id < 63 then (if id < 60 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none)) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))))) else (if id < 73 then (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))))))) else (if id < 117 then (if id < 97 then (if id < 87 then (if id < 82 then (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))))) else (if id < 92 then (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))) else (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))))) else (if id < 107 then (if id < 102 then (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)))) else (if id < 104 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none)) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none))))) else (if id < 112 then (if id < 109 then (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))) else (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none))))))) else (if id < 137 then (if id < 127 then (if id < 122 then (if id < 119 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id = 118 then some localCycle00118 else none)) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)))) else (if id < 124 then (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))))) else (if id < 132 then (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)))) else (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none)))))) else (if id < 147 then (if id < 142 then (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)))) else (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none))))) else (if id < 152 then (if id < 149 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id = 151 then some localCycle00151 else none)))) else (if id < 154 then (if id < 153 then (if id = 152 then some localCycle00152 else none) else (if id = 153 then some localCycle00153 else none)) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![4, 5, 0, 2, 1, 6], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 82 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3072)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 1, 6], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 126 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3073)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 105 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3074)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 22 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3075)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 148 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3076)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 148 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3077)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 66 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3078)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![4, 5, 0, 2, 6, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 47 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3079)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 47 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3080)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 66 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3081)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 0, 6, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 133 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3082)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 3, 2, 6], ![0, 5, 4, 3, 1, 6], ![5, 4, 0, 2, 1, 6], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 109 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3083)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 3, 6, 2], ![0, 5, 4, 3, 6, 1], ![5, 4, 0, 2, 1, 6], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 110 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3084)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 3, 6, 1], ![5, 4, 0, 2, 6, 1], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 156 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3085)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 63 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3086)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![5, 4, 0, 2, 6, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 15 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3087)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 63 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3088)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 101 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3089)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 3, 6, 1], ![5, 4, 0, 2, 6, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 131 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3090)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 63 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3091)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 9 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3092)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 5, 4, 3, 6], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 52 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3093)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 1, 5, 6], ![3, 0, 2, 1, 4, 6], ![3, 0, 2, 1, 4, 5]], proof := .low6 (![118, 60, 50, 24, 71, 33, 120, 25, 146, 0, 83, 39, 31, 114, 88, 61, 94, 95, 84, 135, 132, 95, 127, 102, 122, 151, 57, 54]) }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3094)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 5, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 1, 6, 4], ![3, 0, 2, 1, 5, 4]], proof := .low6 (![118, 60, 50, 24, 138, 152, 35, 23, 16, 128, 6, 108, 149, 114, 3, 155, 108, 44, 18, 41, 108, 13, 48, 108, 98, 11, 124, 108]) }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3095)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 6, 5, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 2, 6, 1, 4], ![3, 0, 2, 5, 1, 4]], proof := .low6 (![118, 90, 144, 67, 81, 112, 70, 79, 56, 129, 10, 130, 149, 27, 100, 142, 72, 97, 123, 116, 45, 58, 26, 87, 100, 93, 77, 5]) }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3096)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 2, 1, 4]], proof := .tail 17 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3097)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 1, 6, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 2, 1, 4]], proof := .tail 17 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3098)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 4, 6, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 2, 1, 6, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 2, 1, 4]], proof := .tail 117 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3099)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 5, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 1, 5], ![3, 0, 2, 6, 1, 4], ![3, 0, 2, 5, 4, 1]], proof := .tail 29 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3100)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 1, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 2, 4, 1]], proof := .tail 29 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3101)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 2, 4, 1]], proof := .tail 29 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3102)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 2, 6, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 2, 4, 1]], proof := .tail 8 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3103)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 2, 1, 5], ![3, 0, 6, 2, 1, 4], ![3, 0, 5, 4, 2, 1]], proof := .tail 136 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3104)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 2, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 0, 4, 2, 1]], proof := .tail 136 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3105)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 6, 2, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 0, 4, 2, 1]], proof := .tail 136 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3106)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 6, 0, 2, 1, 5], ![3, 6, 0, 2, 1, 4], ![3, 5, 4, 0, 2, 1]], proof := .tail 136 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3107)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 6, 0, 2, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 3, 4, 0, 2, 1]], proof := .tail 136 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3108)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 4, 5, 3, 2], ![0, 6, 4, 5, 3, 1], ![6, 4, 5, 0, 2, 1], ![6, 3, 0, 2, 1, 5], ![6, 3, 0, 2, 1, 4], ![5, 4, 3, 0, 2, 1]], proof := .tail 21 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3109)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 4, 6, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 5, 1, 6], ![3, 0, 2, 4, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 55 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3110)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 92 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3111)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 5, 6, 1], ![3, 0, 2, 4, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 19 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3112)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 4, 5, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 5, 1], ![3, 0, 2, 6, 4, 1], ![3, 0, 2, 5, 4, 1]], proof := .tail 119 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3113)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 5, 1], ![3, 0, 6, 2, 4, 1], ![3, 0, 5, 2, 4, 1]], proof := .tail 53 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3114)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 2, 6, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 0, 2, 4, 1]], proof := .tail 53 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3115)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 4, 6, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 2, 6, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 0, 2, 4, 1]], proof := .tail 117 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3116)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 2, 5, 1], ![3, 0, 6, 2, 4, 1], ![3, 0, 5, 4, 2, 1]], proof := .tail 59 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3117)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 2, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 0, 4, 2, 1]], proof := .tail 59 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3118)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 6, 2, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 59 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3119)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 6, 0, 2, 5, 1], ![3, 6, 0, 2, 4, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 59 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3120)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 6, 0, 2, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 59 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3121)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 4, 5, 3, 1], ![6, 4, 5, 0, 2, 1], ![6, 3, 0, 2, 5, 1], ![6, 3, 0, 2, 4, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 125 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3122)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 2, 1, 6], ![3, 0, 4, 2, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 12 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3123)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 96 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3124)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 2, 6, 1], ![3, 0, 4, 2, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 46 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3125)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 32 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3126)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 38 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3127)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 5, 6, 2, 1], ![3, 0, 4, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 133 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3128)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 4, 5, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 5, 2, 1], ![3, 0, 6, 4, 2, 1], ![3, 0, 5, 4, 2, 1]], proof := .tail 30 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3129)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 0, 6, 5, 2, 1], ![3, 6, 0, 4, 2, 1], ![3, 5, 0, 4, 2, 1]], proof := .tail 78 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3130)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 4, 6, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 0, 6, 5, 2, 1], ![6, 3, 0, 4, 2, 1], ![5, 3, 0, 4, 2, 1]], proof := .tail 91 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3131)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 6, 0, 5, 2, 1], ![3, 6, 0, 4, 2, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 150 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3132)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 6, 0, 5, 2, 1], ![6, 3, 0, 4, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 150 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3133)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 6, 4, 5, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 4, 5, 0, 2, 1], ![6, 3, 0, 5, 2, 1], ![6, 3, 0, 4, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 65 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3134)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 12 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3135)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 76 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3136)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 32 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3137)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 2, 6, 1], ![3, 4, 0, 2, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 34 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3138)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 38 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3139)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 0, 6, 2, 1], ![3, 4, 0, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 133 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3140)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 32 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3141)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 0, 2, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 38 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3142)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 0, 6, 2, 1], ![3, 4, 0, 5, 2, 1]], proof := .tail 133 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3143)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 0, 2, 1], ![3, 4, 6, 0, 2, 1], ![3, 4, 5, 0, 2, 1]], proof := .tail 37 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3144)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 6, 5, 0, 2, 1], ![3, 6, 4, 0, 2, 1], ![3, 5, 4, 0, 2, 1]], proof := .tail 137 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3145)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 6, 5, 0, 2, 1], ![6, 3, 4, 0, 2, 1], ![5, 3, 4, 0, 2, 1]], proof := .tail 91 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3146)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 4, 5, 0, 2, 1], ![6, 3, 5, 0, 2, 1], ![6, 3, 4, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 65 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3147)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 4, 6, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 64 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3148)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 143 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3149)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 1, 6], ![3, 0, 4, 2, 1, 5]], proof := .tail 74 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3150)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 4, 6, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 113 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3151)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 2, 6, 1], ![3, 0, 4, 2, 5, 1]], proof := .tail 74 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3152)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 5, 4, 6, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 0, 6, 2, 1], ![4, 3, 0, 6, 2, 1], ![3, 0, 4, 5, 2, 1]], proof := .tail 73 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3153)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 0, 2, 1], ![4, 3, 0, 2, 1, 6], ![3, 4, 0, 2, 1, 5]], proof := .tail 74 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3154)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 0, 2, 1], ![4, 3, 0, 2, 6, 1], ![3, 4, 0, 2, 5, 1]], proof := .tail 74 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3155)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 0, 2, 1], ![4, 3, 0, 6, 2, 1], ![3, 4, 0, 5, 2, 1]], proof := .tail 73 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3156)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 0, 2, 1], ![4, 3, 6, 0, 2, 1], ![3, 4, 5, 0, 2, 1]], proof := .tail 73 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3157)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 5, 6, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 0, 2, 1], ![4, 3, 0, 2, 1, 6], ![4, 3, 0, 2, 1, 5]], proof := .tail 111 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3158)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 5, 6, 4, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 0, 2, 1], ![4, 3, 0, 2, 6, 1], ![4, 3, 0, 2, 5, 1]], proof := .tail 111 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3159)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 5, 6, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 0, 2, 1], ![4, 3, 0, 6, 2, 1], ![4, 3, 0, 5, 2, 1]], proof := .tail 14 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3160)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 0, 2, 1], ![4, 3, 6, 0, 2, 1], ![4, 3, 5, 0, 2, 1]], proof := .tail 14 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3161)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 5, 4, 0, 2, 1], ![5, 6, 3, 0, 2, 1], ![4, 6, 3, 0, 2, 1], ![4, 5, 3, 0, 2, 1]], proof := .tail 2 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3162)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 6, 5, 4, 3], ![0, 6, 5, 4, 3, 2], ![0, 6, 5, 4, 3, 1], ![6, 5, 4, 0, 2, 1], ![6, 5, 3, 0, 2, 1], ![6, 4, 3, 0, 2, 1], ![5, 4, 3, 0, 2, 1]], proof := .tail 49 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3163)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 3, 4, 5], ![6, 0, 1, 2, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 121 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3164)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 3, 4, 5], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 134 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3165)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 1 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3166)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 89 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3167)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 4, 3, 5], ![6, 0, 1, 4, 2, 5], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 80 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3168)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 4, 5, 3], ![6, 0, 1, 4, 5, 2], ![6, 0, 1, 3, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 106 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3169)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 4, 5, 2], ![6, 0, 1, 3, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 40 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3170)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 4, 5], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 1, 5, 3, 2], ![6, 0, 1, 4, 3, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 115 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3171)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 5, 4], ![6, 0, 1, 3, 5, 4], ![6, 0, 1, 2, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 103 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3172)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 5, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 1, 5, 2, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 89 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3173)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 3, 5, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 1, 5, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 1, 3, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 20 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3174)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 5, 3, 4], ![6, 0, 1, 5, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 36 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3175)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 5, 3, 4], ![6, 0, 1, 5, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 68 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3176)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 4, 3, 5], ![6, 0, 1, 4, 3, 5], ![6, 0, 4, 1, 2, 5], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 147 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3177)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 4, 3, 5], ![6, 0, 1, 4, 5, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 28 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3178)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 4, 3, 5], ![6, 0, 1, 5, 4, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 1, 3, 4, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 107 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3179)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 4, 5, 3], ![6, 0, 1, 4, 5, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 2, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 154 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3180)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 4, 5, 3], ![6, 0, 1, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 1, 5, 2], ![6, 0, 3, 1, 4, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 40 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3181)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 5, 4, 3], ![6, 0, 1, 5, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 5, 1, 2], ![6, 0, 3, 4, 1, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 145 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3182)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 2, 5, 4, 3], ![6, 0, 1, 5, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 0, 5, 3, 1, 2], ![6, 0, 4, 3, 1, 2], ![5, 4, 3, 2, 0, 1]], proof := .tail 86 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3183)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 2, 3, 4], ![6, 0, 5, 1, 3, 4], ![6, 0, 5, 1, 2, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 3, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 104 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3184)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 2, 3, 4], ![6, 0, 5, 1, 4, 3], ![6, 0, 5, 1, 4, 2], ![6, 0, 5, 1, 3, 2], ![6, 0, 4, 3, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 68 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3185)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 2, 4, 3], ![6, 0, 5, 1, 4, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 5, 1, 2], ![6, 0, 3, 4, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 42 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3186)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 2, 4, 3], ![6, 0, 5, 1, 4, 3], ![6, 0, 5, 4, 1, 2], ![6, 0, 5, 3, 1, 2], ![6, 0, 4, 3, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 4 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3187)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 4, 2, 3, 5], ![6, 0, 4, 1, 3, 5], ![6, 0, 4, 1, 2, 5], ![6, 0, 3, 2, 1, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 141 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3188)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 4, 2, 3, 5], ![6, 0, 4, 1, 5, 3], ![6, 0, 4, 1, 5, 2], ![6, 0, 3, 2, 1, 5], ![6, 0, 1, 3, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 62 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3189)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 4, 2, 5, 3], ![6, 0, 4, 1, 5, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 2, 1, 5], ![6, 0, 3, 1, 2, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 153 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3190)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 4, 5, 2, 3], ![6, 0, 4, 5, 1, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 2, 1, 5], ![6, 0, 3, 2, 1, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 99 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3191)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 4, 2, 3], ![6, 0, 4, 5, 1, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 2, 5, 1], ![6, 0, 3, 2, 4, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 75 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3192)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 4, 2, 3], ![6, 0, 5, 4, 1, 3], ![6, 0, 4, 5, 1, 2], ![6, 0, 3, 5, 2, 1], ![6, 0, 3, 4, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 85 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3193)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 5, 4, 2, 3], ![6, 0, 5, 4, 1, 3], ![6, 0, 5, 4, 1, 2], ![6, 0, 5, 3, 2, 1], ![6, 0, 4, 3, 2, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 7 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3194)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 3, 2, 4, 5], ![6, 0, 3, 1, 4, 5], ![6, 0, 2, 1, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 51 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3195)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 3, 2, 4, 5], ![6, 0, 3, 1, 4, 5], ![6, 0, 2, 1, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 69 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3196)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 3, 2, 4, 5], ![6, 0, 3, 1, 5, 4], ![6, 0, 2, 1, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 43 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3197)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 3, 2, 5, 4], ![6, 0, 3, 1, 5, 4], ![6, 0, 2, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 140 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3198)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 6, 2, 3, 4, 5], ![0, 6, 3, 5, 2, 4], ![6, 0, 3, 5, 1, 4], ![6, 0, 2, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 2, 1, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 139 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 3199)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (3072 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 3072 ≤ id.val) (hhigh : id.val < 3200) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 3072)) = true := by
  let j : Fin 128 := ⟨id.val - 3072, by omega⟩
  have hsum : 3072 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (3072 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard024
