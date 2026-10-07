import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard011
open N4R2RowDataReplay

-- Original cycle 0409d2e0e3356f0b054eeb44963f378d43802019513f669b264e8c60c13c79d1; original global index 318.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 7 2, .triangle 12 1, .corridorLower 4 5]

-- Original cycle 04334f629895e1bde1304252fe7c7d413421c2e21f58ad77212f2c57739a8378; original global index 329.
def localCycle00001 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 4, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 04528709b45fb39109e2031928def2fe0cbf5a5c448a56123e44082ebb780609; original global index 343.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 068aa69abed3c7e1b65d90552b9374ddaa77ba97b4e9a94a95bb5b8be07aba6e; original global index 538.
def localCycle00003 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .gapLower 3 1, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 0a1815b80555f571cec55a99d01ef283033d8e472e4159c3f01265f97aa07ca4; original global index 814.
def localCycle00004 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 0a6b47893c82e7374a608ee743f76cd7e8eb6d203d36f28ecba78a1502470627; original global index 829.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 0e0dcf95a94e86b464f51fadd03fb3b76364e7e9c5a5eba6a1f40b2969a49660; original global index 1104.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 0e52dac8f445dc6f211c4e8a52601baf53d6ba0e038ce64c3b93eb950af04b1a; original global index 1128.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 0e7d6162e60b0730aaa1a85b787e3873c87d3e98566a99802491137ab3f4d1f2; original global index 1145.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 0f4cf3f5ebd16c52926900e4d1d7401d320818b3cbd765a0354551529860af2e; original global index 1216.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 111a2c01b9baeaa9cf7436c5e3934a4ca297bd3aabfa0ae56a7f5f86f47162db; original global index 1365.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 11d018d74c8b88e48643a3767e00f2721fdeb463568d32b6ea6f4604ed5bf63c; original global index 1420.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 12f252847fdbcde56d3953677430447c5724755577df24e38483d0a5c35a5c13; original global index 1492.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 18edf934bac464e38492c805ea43ec14556ae26940ef6afa212666ffdd84f517; original global index 1946.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 20 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 1a90a6c5b86b4a76eb51ae70fdf175aa7e4be69b695a2b14ee2239227b1e1d1b; original global index 2068.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 1ce35ca6175e49577be5ecb4d53bebd6a733c51f71cb3b13d2f1c5c55f6d295b; original global index 2225.
def localCycle00015 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 1ce58b3d8a89a61adf0191db6c78a4a90800bb1e30fbdd819edab05791291ed4; original global index 2228.
def localCycle00016 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 203eb9f12f55c8269ec00b563ba4464b8d51969c1b9f4c88256fcf9e7d843c0b; original global index 2470.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 2, .gapLower 6 2, .triangle 8 2, .gapLower 6 0]

-- Original cycle 212a57f01a6488c91385b6216b8e01996dee9eb572f12b6f85c0b39cf3d2eaa4; original global index 2541.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 21cb4fedccac8233da105e5be3ae96865783fc114479c0c29e083b528153d5ef; original global index 2591.
def localCycle00019 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 3 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 19 0, .triangle 25 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 22816603a88b1ba9a19a47512afec1cc288c0606b5dda7fe632cad5298174ead; original global index 2641.
def localCycle00020 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 22b2a17829db1f8c1187d53aed8488eaa38e698b7a3f6c81ca65965e2a64cd3d; original global index 2660.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 22e09ae17bcdda30d461859e5e4879dd8b95ab91d44817dcb1c301a94f790f3b; original global index 2672.
def localCycle00022 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 1, .gapLower 3 1, .gapLower 0 2]

-- Original cycle 25671f91f6e70f85da07223085d49baf010cfa71886305f866e8b1b2cb802cbd; original global index 2877.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 27c497859e27e7c6e286c11c6e6a6a56280054e21d89d59eb630e39e19fd4fa7; original global index 3040.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 287ebcfa86ef467476633cb2a2193d4cc6a318dc2023126a9ba7e6f31ac0a3cd; original global index 3102.
def localCycle00025 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 3 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 33 1]

-- Original cycle 29a9d9132bec99606111fe730c0badd1c79d51c779c5c7da452adc4edd99d111; original global index 3180.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2ed568a02f45c2703d51543f2fcd6fdc1616711a3830f4d1268492f09838f1f1; original global index 3583.
def localCycle00027 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 308d5779c7712de9e8f869d1a2acb24845d309d83171a80ce7ed47db77770289; original global index 3701.
def localCycle00028 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .gapLower 3 1, .gapLower 0 2, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 30c74e5bd7c02d8fe3f832692c5997689fcdebbc515b535d6a401260d1e9fe20; original global index 3721.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 32586129e4706857a632092772467ea9318dd12019756c815f96e5634c4c6336; original global index 3849.
def localCycle00030 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 18 0, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 36f6a0ecd3bcb12407317e763130638350bc1cbf378fe4676c0829299ed91500; original global index 4220.
def localCycle00031 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 18 1, .gapLower 6 1, .triangle 13 1, .triangle 9 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 38a0ac3a31918bdfdae4e5a84703ab9c5c63f2bda9712d4f2a560abe1548cac8; original global index 4355.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 399542539c1ba36b45264b08c37635a85a6203d864d5f293143e7855b5adf56f; original global index 4438.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3a07d5937c228a770b60958b238de0d8c779488cedbec72d8249b360db280515; original global index 4477.
def localCycle00034 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 3a79cb82e5697c44b10177e3e7d1e7fedb61770073bfcdb856772d9445a685d4; original global index 4514.
def localCycle00035 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -3]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .triangle 5 0, .gapLower 0 1]

-- Original cycle 3b0e2261671aca795c6aeb2b6b284ddca8f524873c1366c2343df43dabdb7481; original global index 4564.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3be2f5016d6c52126c751219629e3869dfb0079bd6554e71978e26209ea15bca; original global index 4638.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 2, .triangle 20 0, .triangle 26 2, .triangle 7 2, .triangle 12 1, .corridorLower 4 5]

-- Original cycle 435f60ab6535a505bedc43ce9e6f825fc87dd4af2cbca3836d3a4c3a190c4b5a; original global index 5200.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 4445261ebf060ceb43177876bee9d228eb07d751332efce10854593fb1ff3f29; original global index 5285.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 44633a6873ab2a519c1b8346d4954651d407ca8533ddad2b55d40d8ed2ff24f4; original global index 5296.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 2, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 44b08403616d0ec73b0c5c77e2b0da1282826068fa9a664d93b1268829f1a2db; original global index 5325.
def localCycle00041 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .gapLower 4 2, .gapLower 0 4, .gapLower 0 3, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 45fa4f56a885d9243b8e7d14f88fb0b78a55a52cce5f4c085cf387d5f111b350; original global index 5413.
def localCycle00042 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 6, .theta 6]
    constant := ![3, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 11 2, .gapLower 6 0]

-- Original cycle 460fd9d1d731eab3a74dd77dfe4211a1637aa8ba6ab8609bba8f001bcfa02b8f; original global index 5421.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 4731b04a52d3b9b81a239c8704fc4d1682d5a9ca1db2704d4a091b89173b9c6f; original global index 5519.
def localCycle00044 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 47a5c9a497c64edab4deba20bfc9ae9025d8058cd45178e64af390eb8c7435c0; original global index 5544.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle 4974f9986217de0466465703ac3b95532588be56a723f3e9266bc4e6cf2ea5cc; original global index 5692.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 49f0085e798867f1aeb3e65be446e8e9b4360425d6e0229ff0312196437c3a32; original global index 5738.
def localCycle00047 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 28 2, .triangle 7 2, .gapLower 0 3, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4a373a4c2889d846287b363f8f6f788ccce42dbafd8d13da1085dc773591f051; original global index 5754.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 50f8cd7cb83994f6b4eac2cc0aa6f5c3b0f63db2915ba2c6555c89a0dad1e6c4; original global index 6291.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 21 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 51724c97402204717d37f842015698d10c972520283791c09414f66749e82ddc; original global index 6332.
def localCycle00050 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 28 2, .gapLower 5 2, .gapLower 0 3, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 542e7f357ca4ea901cee4413a2a9b83ba3b1f2ac18d88b53331c5b6d4b5914bd; original global index 6522.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 560b76db6d6f50a468fee6dbb59a5db8832debc700688f6f475e9f89ab76bce9; original global index 6675.
def localCycle00052 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 0 3, .distance 0 2, .distance 0 1]
    constant := ![2, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .gapLower 3 1, .gapLower 0 2, .gapLower 0 1]

-- Original cycle 6214165e3d39741c9d539a01ec3c186ce143a5aa57bf60d472b376f19e526f4c; original global index 7658.
def localCycle00053 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 6322c91850caad9b4d8aef6dbd4d6e66af35866d20f11711f37cd6800aca6229; original global index 7731.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0]
    constant := ![2, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false] }
  origin := ![.gapLower 0 6, .triangle 13 1, .gapLower 0 4, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1]

-- Original cycle 6ac38ce34544287d42d9ce2997d4504b59ffd91d0c41b74a50a8eb131fe8706b; original global index 8310.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6c39e8d96aab90e434d08705e14ed98d607f402fa710615792a5208c5f1c89d7; original global index 8431.
def localCycle00056 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .gapLower 1 3, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 6de8831c676dcd84141759a4ad2a50d26c577abc8bd66117b5491b4093bb7ee6; original global index 8535.
def localCycle00057 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 6eb5f26ac86f2f120b3ade20d3b30a727eb6040382f4a73dae2e72cc31477321; original global index 8590.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 32 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 6f07abf71490ebd876dd0219841890d8a98fc9302991703ec07f6080e8c26a22; original global index 8611.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 6feffb507363e3f7f4cfe06bcd5681fde07420539e2cb00ec5b6773be59bf2ba; original global index 8679.
def localCycle00060 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 1 3]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 20 2, .gapUpper 5 5, .triangle 33 2, .triangle 27 0, .triangle 25 0, .triangle 19 0]

-- Original cycle 71f7441fbb3768a03975d077ea6ac3f7e39fc4bad818d4ca9852725e96ea2fe1; original global index 8832.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 29 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 7317686d83e0f3b3200cf1084ed0fddde65266eda03a84b355e8ae1c845703b3; original global index 8914.
def localCycle00062 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 6 2, .triangle 12 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 73510f3f7151d630fe3f1b4e1e3334d20a7accb694658a8f09be7cd4ce7b3ae8; original global index 8926.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 7392e48ac379b717e22a0a4c14245ffc9a0da2fb0be67cb23ddb88ca0a48293f; original global index 8961.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 766343f43fc61480162db1a1231e128cf79279f448a4409cf7a066941e673502; original global index 9164.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 7799d73c8c8eeb323c0901c8d30ea752f6e465357a02e42bce14ffd03f898be1; original global index 9253.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 7bf8a56485bdd76eb9a7db70ca84e40cf59f6fd6a4a801ba30061351dd35264b; original global index 9588.
def localCycle00067 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -2, 0, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 6 2, .gapLower 0 4, .triangle 10 1, .triangle 5 1, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 7e700f18a15088f4c77c5fad4e2831a5c99df6e4a01184ead22b78c6c7aef532; original global index 9821.
def localCycle00068 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .gapLower 2 4, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 802a21cefe1ed5766816b10467685225ae72c59bb5c1285fce09501c35b35b61; original global index 9943.
def localCycle00069 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 5 0, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 8362e23a9df1dd76bd6044d3138d307acf887d8c634ca52434d83c3bbf1430b1; original global index 10189.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 8486744b86d69cee65a680d626f68fc2576e8536eaae24178dd22df69556e939; original global index 10290.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 84ced9e2ea5818122ea5844a53812f314b5d5303c2220c0ee5f58b84778334b8; original global index 10313.
def localCycle00072 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1]
    constant := ![2, 0, -1, -2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 1 1, .gapLower 3 2, .triangle 5 0, .gapLower 0 1]

-- Original cycle 85103b8d055dd33381eebdd5fdd1e383e7bf0340ccdfa18e9995d01bf42168db; original global index 10327.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .gapLower 6 2, .triangle 8 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle 8604cf705b5f34a506fe383518c4414a160d1fe5427b48382bfd59266d48a708; original global index 10396.
def localCycle00074 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 20 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 87933b6703d642ff5b694e1fc0cc5900b9bf69cb6f3d0b3d8a8335e7c98e5332; original global index 10513.
def localCycle00075 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 28 2, .gapLower 5 2, .gapLower 0 3, .triangle 5 1, .triangle 0 1, .gapLower 0 0, .thetaLower 0]

-- Original cycle 886d04b1acc0b8039cbf8f874b3cb295c3a916cae978c35688d369e5d36986c5; original global index 10570.
def localCycle00076 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 17 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 15 0]

-- Original cycle 8b3d7e26bb0591d10e16447f6d9a54c5597eca9b205cf30b36c7aacfc3c13f35; original global index 10788.
def localCycle00077 : Cycle where
  length := 4
  data := {
    node := ![.distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 3 4]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 3 4, .gapUpper 5 5, .gapLower 6 5, .triangle 32 0]

-- Original cycle 8f9299f038a17d7a0f1f05703a78c708d920aa6270d01b3e250508071d4eef46; original global index 11111.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 5, .distance 4 5, .distance 0 4]
    constant := ![-3, 0, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 0 4, .gapLower 5 1, .gapUpper 4 1]

-- Original cycle 90baed6f0949210008917356810a36ed32bbe6908602d16ac13f0257cd149bcc; original global index 11207.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 91ac8848afcdced1b3630d50f437184d957080e134e55aed31c397215fc76759; original global index 11289.
def localCycle00080 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 957c03792a88374e0ccbd026d9834d3d93c0aa29dcbaab528aa77896d5b69976; original global index 11618.
def localCycle00081 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 968a3c7fa7cf468b759d6d4a5e9f68b116e8eae262e3868ae1f0074cce679092; original global index 11707.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 997026b3bc39def187caaf938c349d8d4d05c4cd69cabbf21529a491962d6c87; original global index 11918.
def localCycle00083 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle 9b558feee4e058657947596e039098cc084e51d47fdeb0352ff402bcaa32370c; original global index 12080.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 6, .theta 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -3, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 9f95f3c05496bd2aa8624465d0f9979868ab376f6f9a8f859b0c9ce58a6b1f77; original global index 12419.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle a1297beb1effae9fd46175c8c9d5f610e1a4d7b433961f00b57a64a1677a18f0; original global index 12533.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a26a384325e5ad3cd0e8a45a31a534a3885779e8d8326c4f4ee1e4ca88916fc3; original global index 12634.
def localCycle00087 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![2, -2, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .gapLower 0 5, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle a3ff470e14a84742ef82d2e61efe4b33962d8183fa00ebb39fca1a6becc5d612; original global index 12748.
def localCycle00088 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 2 3, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a49084d64fa8544432b827239d78cc6b05c592fb84c4e750f3b8f929d5234c1e; original global index 12791.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 20 1, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle a4af7fdcb39c435eb8705b545339b5f193ea1cd691eb5620be6a49f7342efdba; original global index 12799.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 2, .distance 1 2, .distance 2 6, .distance 0 6, .theta 6, .theta 5, .zero]
    constant := ![0, 3, -1, -2, -2, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 2, .corridorUpper 1 2, .triangle 18 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaLower 5]

-- Original cycle a4cce42e079e92e4d9065f479f6055e9f01ba77f4c7398672528dbfe0575d2c0; original global index 12808.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a680bcbd0bd9d104e66e4a7af17ed380dd0a69de627b9196e8732c7c9b8eb592; original global index 12934.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 10 0, .corridorLower 0 3, .thetaLower 0]

-- Original cycle a7cb37a65579ca5cb4c26e640e375c61a04780ad150f080f6aa2b30bc292568d; original global index 13055.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 21 0, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle a7fbf769e27142290c556b5c987df530ab951d6ea0ae9281e3a4119295b10081; original global index 13079.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -2, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .triangle 13 1, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle adf6eb078f849f28da28f2518027414f09c8d6093f0998f51bab7fd0626c89c4; original global index 13572.
def localCycle00095 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, true, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 12 2, .gapLower 0 3, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle ae75addfb23f94cb8548440322fdc0077bb803b6861e3fc88dbf1dbfd674b2ca; original global index 13618.
def localCycle00096 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 27 0, .triangle 32 1, .triangle 23 0, .gapLower 1 4, .gapLower 1 3, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Original cycle af0c3318a192f4c148e40527be5f51cd06386ddf206cab5a143427e9362a939c; original global index 13663.
def localCycle00097 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 6, .distance 0 2, .theta 2]
    constant := ![3, -1, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .gapLower 6 1, .triangle 8 1, .gapLower 2 0]

-- Original cycle af95bc5d69736c1f1f9b91e177ffb73455d0194407277ac7c6919b57496eab46; original global index 13716.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle b1cf02857d848b599fdf56c3d4b6e658714ebf54d8ef50403083b049ff1cfb38; original global index 13896.
def localCycle00099 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 20 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle b23d7664dfb752893a23cdc7f3389328e762810b42992a006efa299043e52c23; original global index 13929.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 33 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle b2ef40b259efb1576c35aecfb03dcd1d2f01e61b22bb75c232916f2f6271fe5b; original global index 13984.
def localCycle00101 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 2 6, .distance 1 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 18 2, .gapLower 6 2, .gapUpper 2 5]

-- Original cycle b3ed8028fff3d37b2ee05ebf3dfeb5bbd57f31af82920257f4d96b2dc857616d; original global index 14051.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle bd871d10e0c3d31dabaf3a0ee60cff76cd8fd80ef6549c4262e0ac1af2f0df01; original global index 14784.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 2 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle bda659af50738dd02e9c9d1aba13fca736a95df92a8627a6a5ddac35cdd5af42; original global index 14794.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle bea8efdee286331f3c30a088235472d355afcd975435fb7736f8ddfa6187afe7; original global index 14874.
def localCycle00105 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle bf4a9c1d828a46258e7b73e37634752f12ef5a8c27673bcf349a53cd2a588996; original global index 14930.
def localCycle00106 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![4, -2, 0, -2, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .gapLower 6 4, .triangle 27 2, .gapLower 6 1, .triangle 13 1, .triangle 12 0, .corridorLower 4 5]

-- Original cycle bfd362374af2bdf0db1c65b8044101b9831a370845ebdeb2d66eadabfa843a76; original global index 14966.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle c3d77e1582febb65bcc4f075f6949770f058685d2c2773f61a7ab928e33acdd7; original global index 15278.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 1 3, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .triangle 32 0, .triangle 19 0, .triangle 15 1, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle cbda04c54e6763552f97942d9102597d839a8372e406d58497f829ffc80d3243; original global index 15931.
def localCycle00109 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -3, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaLower 3]

-- Original cycle cd4abd68489b929f7adf1998d835ef80d6a254d1e419bc44419f56952847c175; original global index 16047.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 19 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle ceffda76076353e9192fbb3248ad38d14862ecb9d95d917420d7a1c7f5a48ba4; original global index 16152.
def localCycle00111 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 0]

-- Original cycle cfab64ca5c223fe6d00cb33b88a667ba9277be2dc5f011097654ae3f0075728e; original global index 16206.
def localCycle00112 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .corridorLower 0 2, .thetaLower 0]

-- Original cycle cfb8e2544ec97e0ea43942dc5b696a695f44cd3a6e3cb7e4954e763be5d23a97; original global index 16211.
def localCycle00113 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 5, .gapLower 6 4, .triangle 32 1]

-- Original cycle d0e41690163c80bb86575ced0d25daccbf5b793dd2d65e11c58ffbd4f284aabc; original global index 16310.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle d2510646bcd7d242b03c593a0f2999abcd4311896578eeb84fae3ce407ff7bc1; original global index 16407.
def localCycle00115 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle d6f1c80d582d83696cbeffe3a14e3fcad3f1aafbf4a82de54cec77ca5846f157; original global index 16780.
def localCycle00116 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 1 4, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 23 0, .triangle 16 1, .triangle 25 1, .triangle 26 0, .triangle 10 2, .triangle 12 1, .corridorLower 4 5]

-- Original cycle dcce1c4c59cfba3121712a64640ef664e51d6c261af21dac4684aa8ae4f2844a; original global index 17255.
def localCycle00117 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 5, .distance 0 5, .distance 0 3, .distance 0 2, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 28 2, .gapLower 5 2, .gapLower 0 3, .gapLower 0 2, .corridorLower 0 2, .thetaLower 0]

-- Original cycle dd326c1772c993d8a577c5e47586e66a06cc132936c852324cd6c62c61065136; original global index 17295.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle e00d08190a0b7e06e719c943d0ed3d712a6edf91bfbf9025153909677ffe3dde; original global index 17514.
def localCycle00119 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -3]
    coefficient := ![0, 0, 0]
    strict := ![true, false, false] }
  origin := ![.gapUpper 2 1, .gapLower 3 1, .gapLower 0 2]

-- Original cycle e1454bde9f681d18d54e363c51185edda3b06745487f9470d10176142eca14a4; original global index 17617.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle e29c6e5bf2a6e058ce34e746548105c71d9890051eebf22cc2468350fafa31f3; original global index 17721.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle e2e846e23e73dcb10a1d0de9ec1a8f85abe974e49eef2cf8010adccf7fbcda91; original global index 17749.
def localCycle00122 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .gapLower 4 2, .triangle 12 0, .corridorLower 4 5]

-- Original cycle e2f0c705c609eb2328bca722074275b9bdb45bcd93e5b55001afc6f44db43441; original global index 17750.
def localCycle00123 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .theta 3, .zero]
    constant := ![0, 2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 34 2, .gapLower 6 4, .gapUpper 3 6, .thetaLower 3]

-- Original cycle e317dec798ba1162ca84bc8085c7a46987f7950e79026ba8319210c85791819f; original global index 17757.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 17 0, .triangle 26 1, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle e364b9883d887a508bcd08e81c7d82c29f58ea339c678d8a4739008e1df626df; original global index 17782.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle e608b996192634a9df721c72da2846d34a03dd0006e2e81d6dfb667ec462ac40; original global index 18003.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle e8b2312fe4316a8ad005cea6d8e3e371c0835a4e33d3b1c6129eae129ed46eeb; original global index 18188.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 0 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 17 0, .triangle 7 2, .triangle 12 1, .corridorLower 4 5]

-- Original cycle e8d220bc9ee9bdc5970355a2f6a1260f064645bec52552f54c234f893bfd1dc3; original global index 18194.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .distance 0 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .theta 0]
    constant := ![1, 0, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, true] }
  origin := ![.gapLower 0 6, .triangle 13 1, .triangle 12 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .thetaNext 0]

-- Original cycle e932e0a731f18bf49b123763e8cbba8e686da6277d27459cf492da033febebcd; original global index 18220.
def localCycle00129 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, 0, -2, -2, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, true, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 0 5, .gapLower 0 4, .triangle 10 1, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f02439739e55ddfb6d6631df6f0996736db7e4cd39a947bc8fa73d3c1bdb2161; original global index 18733.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle f19d74d57c656d553fdc5dcfff3102b887f051e7f3538ba303f902a67eac1210; original global index 18839.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f2ff647491dbee5b766a8b68a543769f396d940bce895398efb597f552013235; original global index 18944.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 2, .triangle 24 0, .triangle 33 2, .triangle 32 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f33572f5fee93dd92994d85e90903b0c955630194e500fa8f2148115b1fdf039; original global index 18966.
def localCycle00133 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 0 3, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .triangle 10 0, .triangle 5 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f5cb0d8f1edb652ccff7498deb0c8124cc1ec8f6365dbb9acaf38dcaa10d8bad; original global index 19176.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .gapLower 0 0, .thetaLower 0]

-- Original cycle fc3f7737d1391b84bc8b1aec0e1cad3d916e464880b0264c0a19f4614693aa28; original global index 19702.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .gapLower 1 4, .triangle 15 1, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Original cycle fcdb830c0b814c3275ae684e9b98f02153906857fb1ab5c81f094cb4498fe0db; original global index 19761.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 13 0, .triangle 12 0, .corridorLower 4 5]

-- Original cycle fef47a891689ad5c12d346067a8dc5e9abb7aa82456abc734a28e0435dce06fe; original global index 19934.
def localCycle00137 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle ffcd02b12386075cf49044efa9df022a4d3893a09f9ee612e8ff3218268ed9ae; original global index 20008.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 19 0, .triangle 20 0, .corridorLower 3 5]

def library : Library := fun id => if id < 69 then (if id < 34 then (if id < 17 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))))) else (if id < 25 then (if id < 21 then (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 29 then (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))))))) else (if id < 51 then (if id < 42 then (if id < 38 then (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 46 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))))) else (if id < 60 then (if id < 55 then (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))))) else (if id < 64 then (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))))))) else (if id < 104 then (if id < 86 then (if id < 77 then (if id < 73 then (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))) else (if id < 81 then (if id < 79 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 83 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none)) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)))))) else (if id < 95 then (if id < 90 then (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none))))) else (if id < 99 then (if id < 97 then (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))) else (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id = 103 then some localCycle00103 else none))))))) else (if id < 121 then (if id < 112 then (if id < 108 then (if id < 106 then (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))) else (if id < 116 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id < 120 then (if id = 119 then some localCycle00119 else none) else (if id = 120 then some localCycle00120 else none)))))) else (if id < 130 then (if id < 125 then (if id < 123 then (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))))) else (if id < 134 then (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![0, 3, 5, 1, 4, 6], ![0, 2, 1, 5, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 2, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 80 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1408)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![0, 3, 5, 1, 4, 6], ![0, 2, 1, 6, 5, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 2, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 82 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1409)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 5, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 2, 1, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 127 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1410)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 2, 4, 6], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 2, 1, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 0 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1411)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 83 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1412)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 70 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1413)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 5, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 3, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 130 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1414)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 1, 6, 3], ![0, 4, 2, 1, 5, 3]], proof := .tail 130 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1415)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 6, 5, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![0, 4, 2, 5, 1, 3]], proof := .tail 7 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1416)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 6, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 59 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1417)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 3, 5, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 6, 1, 3], ![0, 4, 2, 5, 3, 1]], proof := .tail 89 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1418)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 3, 5, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 59 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1419)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 3, 5, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 1, 5, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 1, 3], ![0, 4, 5, 3, 2, 1]], proof := .tail 124 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1420)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 4, 6], ![0, 5, 1, 2, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 76 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1421)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 4, 6], ![0, 5, 1, 2, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 68 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1422)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 2 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1423)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 96 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1424)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 3, 6, 4], ![0, 5, 1, 2, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 24 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1425)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 3, 4], ![0, 5, 1, 6, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 93 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1426)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 20 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1427)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 14 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1428)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 104 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1429)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 5, 6, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 16 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1430)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 3, 4], ![0, 6, 5, 1, 2, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 10 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1431)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 4, 3, 6], ![0, 5, 1, 4, 2, 6], ![5, 0, 1, 3, 2, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 60 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1432)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 4, 6, 3], ![0, 5, 1, 4, 6, 2], ![5, 0, 1, 3, 2, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 13 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1433)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 4, 6, 2], ![5, 0, 1, 3, 6, 2], ![4, 0, 3, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 138 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1434)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 4, 6], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 0, 1, 6, 3, 2], ![4, 0, 3, 2, 1, 6], ![0, 1, 4, 3, 2, 5]], proof := .tail 135 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1435)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 3, 6, 4], ![0, 5, 1, 6, 4, 3], ![0, 5, 1, 6, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 2, 1, 6], ![0, 4, 1, 3, 2, 5]], proof := .tail 36 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1436)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 6, 3, 4], ![0, 5, 1, 6, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 49 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1437)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 49 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1438)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 3, 4], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 29 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1439)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 5, 6, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 137 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1440)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 3, 4], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 1, 4, 2], ![5, 0, 6, 1, 3, 2], ![4, 0, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 64 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1441)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 3, 5, 1, 4, 6], ![0, 2, 5, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 57 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1442)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 3, 5, 1, 4, 6], ![0, 2, 5, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 2, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 37 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1443)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 3, 5, 1, 6, 4], ![0, 2, 5, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 105 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1444)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 2, 6, 4], ![0, 3, 5, 1, 6, 4], ![0, 2, 5, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 30 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1445)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 6, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 130 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1446)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 136 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1447)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 5, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 112 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1448)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 3, 5, 6, 1, 4], ![0, 2, 6, 5, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 74 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1449)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 3, 6, 5, 1, 4], ![0, 2, 6, 5, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 43 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1450)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 6, 3, 5, 1, 4], ![0, 6, 2, 5, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 6 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1451)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 4, 6], ![0, 5, 2, 1, 4, 6], ![5, 0, 1, 2, 3, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 92 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1452)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 4, 6], ![0, 5, 2, 1, 6, 4], ![5, 0, 1, 2, 6, 3], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 120 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1453)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 2, 4, 6], ![0, 5, 3, 1, 6, 4], ![0, 5, 2, 1, 6, 4], ![5, 0, 1, 6, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 1 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1454)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 2, 6, 4], ![0, 5, 3, 1, 6, 4], ![0, 5, 2, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 1, 2, 3, 5]], proof := .tail 85 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1455)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 6, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 1, 6, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 130 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1456)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 23 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1457)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 114 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1458)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 5, 3, 6, 1, 4], ![0, 5, 2, 6, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 12 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1459)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 5, 6, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 114 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1460)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 5, 6, 2, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 59 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1461)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 2, 4], ![0, 6, 5, 3, 1, 4], ![0, 6, 5, 2, 1, 4], ![5, 0, 6, 1, 2, 3], ![4, 0, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 63 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1462)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 3, 6], ![0, 5, 4, 1, 2, 6], ![5, 0, 3, 1, 2, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1463)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 4, 6, 3], ![0, 5, 4, 1, 6, 2], ![5, 0, 3, 1, 2, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 110 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1464)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 4, 3, 6], ![0, 5, 1, 6, 4, 3], ![0, 5, 4, 1, 6, 2], ![5, 0, 3, 1, 6, 2], ![4, 0, 3, 2, 1, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 39 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1465)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 4, 6, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 1, 2, 6], ![4, 0, 3, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 55 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1466)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 4, 6, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 1, 6, 2], ![4, 0, 3, 2, 1, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 45 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1467)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 2, 1, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 33 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1468)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 15 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1469)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 34 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1470)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 1, 2], ![4, 0, 3, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 137 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1471)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 2, 6, 4, 3], ![0, 5, 1, 6, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 1, 2, 5]], proof := .tail 102 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1472)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 38 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1473)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 4, 3], ![0, 5, 6, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 132 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1474)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 137 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1475)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 2, 4, 3], ![0, 6, 5, 1, 4, 3], ![0, 6, 5, 4, 1, 2], ![5, 0, 6, 3, 1, 2], ![4, 0, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 125 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1476)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 1, 5, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 0, 2, 1, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .low0 (![134, 35, 119, 50, 78, 109, 128, 72, 28, 75, 67, 69, 69, 52, 72, 72, 72, 72, 117, 22, 22, 3, 41, 95, 47, 129, 54, 87]) }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1477)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 1, 5, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 0, 2, 1, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 79 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1478)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 4, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 1, 6, 5, 4], ![5, 0, 2, 1, 6, 3], ![4, 0, 2, 1, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 98 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1479)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 5, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 0, 2, 1, 3, 6], ![0, 2, 1, 3, 4, 5]], proof := .low6 (![84, 97, 101, 91, 113, 4, 121, 90, 17, 111, 42, 77, 131, 94, 31, 106, 77, 108, 73, 65, 77, 40, 26, 77, 48, 25, 123, 77]) }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1480)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 5, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 0, 2, 1, 3, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 53 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1481)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 4, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 6, 5, 4], ![5, 0, 2, 1, 6, 3], ![4, 0, 2, 1, 6, 3], ![0, 2, 1, 4, 5, 3]], proof := .tail 103 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1482)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 5, 6, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 2, 1, 3, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 118 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1483)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 6, 5, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 2, 1, 6, 3], ![0, 2, 4, 1, 5, 3]], proof := .tail 122 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1484)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 1, 6, 5, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 2, 6, 1, 3], ![0, 2, 4, 5, 1, 3]], proof := .tail 51 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1485)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 6, 1, 5, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 2, 6, 1, 3], ![0, 2, 4, 5, 3, 1]], proof := .tail 100 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1486)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 5, 6, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 2, 1, 3, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 61 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1487)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 5, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 2, 1, 6, 3], ![0, 4, 2, 1, 5, 3]], proof := .tail 61 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1488)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 2, 6, 1, 3], ![0, 4, 2, 5, 1, 3]], proof := .tail 61 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1489)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 3, 6, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 1, 6, 5, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 6, 2, 1, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 126 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1490)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 1, 5, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 2, 6, 1, 3], ![0, 4, 2, 5, 3, 1]], proof := .tail 136 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1491)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 3, 5, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 1, 5, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 6, 2, 1, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 107 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1492)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 3, 5, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 1, 5, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 6, 2, 1, 3], ![0, 4, 5, 3, 2, 1]], proof := .tail 100 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1493)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 4, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 5, 1, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 0, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 57 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1494)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 4, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 5, 1, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 0, 2, 3, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 56 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1495)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 4, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 1, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 0, 2, 3, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 57 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1496)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 4, 6, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 1, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 0, 2, 3, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 86 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1497)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 6, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 1, 6, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 2, 3, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 62 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1498)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 3, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 6, 1, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 2, 3, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 20 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1499)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 5, 6, 1, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 2, 3, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 8 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1500)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 4, 6, 1], ![0, 2, 6, 5, 1, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 2, 6, 3, 1], ![0, 2, 4, 5, 3, 1]], proof := .tail 74 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1501)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 6, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 1, 6, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 27 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1502)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 2, 3, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 136 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1503)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 5, 6, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 2, 3, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 8 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1504)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 5, 6, 4, 1], ![0, 2, 6, 5, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 2, 6, 3, 1], ![0, 4, 2, 5, 3, 1]], proof := .tail 74 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1505)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 3, 6, 5, 4, 1], ![0, 2, 6, 5, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 2, 3, 1]], proof := .tail 43 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1506)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 6, 3, 5, 4, 1], ![0, 6, 2, 5, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 6, 2, 3, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 6 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1507)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 1, 6], ![0, 5, 2, 1, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 133 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1508)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 4, 2, 6], ![0, 5, 3, 4, 1, 6], ![0, 5, 2, 1, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 71 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1509)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 1, 4, 6], ![5, 0, 2, 1, 3, 6], ![4, 0, 3, 2, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 99 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1510)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 4, 6, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 1, 6, 4], ![5, 0, 2, 1, 6, 3], ![4, 0, 3, 2, 1, 6], ![0, 2, 1, 4, 3, 5]], proof := .tail 116 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1511)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 6, 4, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 1, 6, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 3, 2, 1, 6], ![0, 2, 4, 1, 3, 5]], proof := .tail 88 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1512)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 3, 4, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 6, 1, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 3, 2, 1, 6], ![0, 2, 4, 3, 1, 5]], proof := .tail 23 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1513)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 5, 3, 4, 6, 1], ![0, 5, 2, 6, 1, 4], ![5, 0, 2, 6, 1, 3], ![4, 0, 3, 2, 6, 1], ![0, 2, 4, 3, 5, 1]], proof := .tail 5 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1514)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 3, 6, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 1, 6, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 2, 1, 3, 5]], proof := .tail 61 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1515)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 2, 3, 1, 5]], proof := .tail 23 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1516)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 20 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1517)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 5, 3, 6, 4, 1], ![0, 5, 2, 6, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 3, 2, 6, 1], ![0, 4, 2, 3, 5, 1]], proof := .tail 5 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1518)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 5, 6, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 9 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1519)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 5, 6, 2, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 9 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1520)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 3, 4, 2], ![0, 6, 5, 3, 4, 1], ![0, 6, 5, 2, 1, 4], ![5, 0, 6, 2, 1, 3], ![4, 0, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 74 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1521)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 3, 6], ![0, 5, 4, 1, 2, 6], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 18 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1522)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 2, 3, 6], ![0, 5, 4, 1, 6, 3], ![0, 5, 4, 1, 6, 2], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 66 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1523)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 2, 6, 3], ![0, 5, 4, 1, 6, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 66 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1524)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 1, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 2, 1, 6], ![4, 0, 3, 2, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 11 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1525)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 21 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1526)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 2, 1], ![4, 0, 3, 2, 1, 6], ![0, 3, 4, 2, 1, 5]], proof := .tail 81 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1527)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 2, 1], ![4, 0, 3, 2, 1, 6], ![0, 4, 3, 2, 1, 5]], proof := .tail 58 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1528)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 4, 6, 1, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 2, 6, 1], ![4, 0, 3, 2, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 115 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1529)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 2, 1], ![4, 0, 3, 2, 6, 1], ![0, 3, 4, 2, 5, 1]], proof := .tail 81 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1530)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 5, 6, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 2, 1], ![4, 0, 3, 2, 6, 1], ![0, 4, 3, 2, 5, 1]], proof := .tail 58 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1531)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 5, 4, 6, 1, 2], ![5, 0, 3, 6, 2, 1], ![4, 0, 3, 6, 2, 1], ![0, 3, 4, 5, 2, 1]], proof := .tail 46 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1532)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 5, 6, 4, 1, 2], ![5, 0, 6, 3, 2, 1], ![4, 0, 3, 6, 2, 1], ![0, 4, 3, 5, 2, 1]], proof := .tail 46 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1533)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 1, 3], ![0, 6, 5, 4, 1, 2], ![5, 0, 6, 3, 2, 1], ![4, 0, 6, 3, 2, 1], ![0, 4, 5, 3, 2, 1]], proof := .tail 32 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1534)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 2, 3, 5, 4, 6], ![0, 5, 4, 3, 2, 6], ![0, 3, 5, 4, 1, 6], ![0, 2, 5, 4, 1, 6], ![5, 0, 2, 3, 1, 6], ![4, 0, 2, 3, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 19 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 1535)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (1408 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 1408 ≤ id.val) (hhigh : id.val < 1536) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 1408)) = true := by
  let j : Fin 128 := ⟨id.val - 1408, by omega⟩
  have hsum : 1408 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (1408 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard011
