import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard110
open N4R2RowDataReplay

-- Original cycle 011a4efb1dce098a2a745d1b995feafdaca868b24b95c33d30e4b19b5787678d; original global index 98.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 026fe39808a19f7dd7235d9b76cb5887f80fd08246aa221e8864ea8565db4a8c; original global index 191.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 039ca8e2f83ecad552a4eea5610ce42bc11556d615a9a22043a2c63cdd13015d; original global index 293.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .gapLower 3 0]

-- Original cycle 0644377e0bd25d49735f171b8d9470be6b198bbaed05b32df6765f9b5af27e31; original global index 518.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 0e582d6683f304801e78800e45d44f743530c7cf45f7597101ff6440474830c9; original global index 1132.
def localCycle00004 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 0faeaa964f1b6c57c059901629d42550a61584fdb00bbd352eca3f9408802735; original global index 1250.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 29 1, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 1d5011eef3b6f3954a0c46f11ab5e9569feab0469680655add17ca190d950060; original global index 2256.
def localCycle00006 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 2c3cb984c3cd840e1b3667f7470d0089592ba6d7b08e86b31b021ab5c893bfe0; original global index 3385.
def localCycle00007 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 0 2]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 6 0]

-- Original cycle 370b5794e2c863d297f09930bcb6686d78220990d07180ee05ddc5d4bd8ca78c; original global index 4223.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 391c843f661a754eca6402ba0d09e83bf9cecd02b09bb072eaa37b256c20e7e2; original global index 4394.
def localCycle00009 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3c417bba8ffdcb6877864a4fe98051f3e9a7cdbb2182f8b27629bef36d9af06e; original global index 4673.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 3e514418f78591cd162da0ecdab00cc8ddd94227e513a3b74a6705ddbeee9edd; original global index 4822.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle 3e86badc3dfc7280c95093fc1afe7d1111711e18c04347220b4cf5e7e59fd20f; original global index 4837.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 41df67104e558bdbd7140f5fe3e90a3277779149b8180688abc385d0986c5677; original global index 5079.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 4461b796f0d4fc5c59e0509c7e492b71de61e990ab4262eb6266f0c1d0274e3c; original global index 5295.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 4614b0fa4a38b73a2dc069d0599a61589bae0d74b230b84a9173eecaad6b153b; original global index 5424.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 470248855675f05ef3a0f1872deb8a583a56650fafd796a010c3c8052d6cd03a; original global index 5503.
def localCycle00016 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .gapLower 4 0]

-- Original cycle 494af8e695dff9cb81f1e578794c5014f06ca857d8dc5e61523e2bc6cdd8fe43; original global index 5676.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 4cf9ddd8babea0b19434615e3097393be5236b183cf46e432e73a68e02e0f719; original global index 5979.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 17 2, .triangle 20 1, .corridorLower 3 5]

-- Original cycle 5c7798e1d83363f9d2a4c171ff288a34c1a666cb0e5c03f9c0e07e2e16cbd5bb; original global index 7200.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 5ee3d6490c1e85855aa301ee673354571dff97cdd541518be845c847c0df71f0; original global index 7385.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 5fcb177eb2f063be607b6688fec5704b3acac05825e5643be0249640a9020f78; original global index 7468.
def localCycle00021 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 660b277dc6f54bd88bb96888963de89035b6ab2956bc6bca745d6bb4eda195c3; original global index 7942.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 68616eef9f45a6ca262c899a47022b44658a9982ccbb631b9e3c07bf406aec10; original global index 8117.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 6b12c8e3148564eed039cbf8a0474eaa731f4ad4bb1042a71619f118c8d65f76; original global index 8335.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Original cycle 6bbe24dfde7c085612d5dc129963be8a80e73e708f59ce267ded2ab3447fd9e8; original global index 8388.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .gapLower 3 0]

-- Original cycle 7092ff457ec17edaac49f3c61b2f0194a12d7cb8d1113a0c2cecf207e5fed50a; original global index 8723.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .triangle 32 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 752a3d64909a715f989599ed64bb545a5e24c578d09072bba278a15d3eafda7f; original global index 9079.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, true, false] }
  origin := ![.triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 32 2, .gapUpper 3 3, .gapUpper 3 4, .triangle 1 0]

-- Original cycle 76d943d5171351a1b506e27269c1fb5c9c068930e15652ee4e47d65c0afc7513; original global index 9199.
def localCycle00028 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 7 0, .triangle 30 0, .triangle 34 2, .gapUpper 4 4, .triangle 6 1]

-- Original cycle 7a6b14b46bc95cf7c0cb35f774ed91df0ea0fdb67a4c4bf3cfe8d6e492345434; original global index 9472.
def localCycle00029 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 7f2a211aa4087970a632f01b39386f83eac362b44a3965b61fd63e1377bf39c0; original global index 9861.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 23 1, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 7fdd82ad8c33a6216cfcc4228a6bdb82ec59bb728da69084044bfdb8c4a94e3a; original global index 9918.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 80a4779abcfbf5fa14f273fc53e9128147ac1e5d77642989c13e33b6afd2bda2; original global index 9987.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 3 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 33 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 8362f9ffd984d4566ad730847b7418dcfb7e92d5f3463ebc8e9350c90bfadac5; original global index 10190.
def localCycle00033 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 87e47127b4198f7083a54753c17f6b39be600963ba28f45e286f22200d4ff0c8; original global index 10531.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle 8841e74162fd7a384c52d69c8f3e0133a28b4a4129ea185f3a1fc9be022b9f8b; original global index 10560.
def localCycle00035 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle 894158a9782ac225abf9398329a454e153b63c8284e8f3d6ab521978d67acc52; original global index 10621.
def localCycle00036 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 8b63b76a928df0698c26ca153875d86ade485b5ae89da5b2bfeb664aa1e2e755; original global index 10801.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1]
    constant := ![0, 0, 0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, true, true, false, false] }
  origin := ![.triangle 2 2, .triangle 6 1, .triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0]

-- Original cycle 932de381ce65293d7eb9320097d28f932c6e0985d102ae147dbdb46774323752; original global index 11413.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Original cycle 96c47bc4b03b0d6f80f635a1baec40beee361855bcc70e8b5c13fca629848987; original global index 11722.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a16c82548ef9a0098817b9595fd7a60e745b1d46713fe328c4565f574790bf4d; original global index 12552.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a602b2882819be4ac24dcd1f1aaae600dbe3f8e241de4b6a3f43fd1a0a611293; original global index 12898.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle a7254c3328022591d7dcce096fe04c8bca1dc2b1e3f0fb3db72ad8371ad94919; original global index 12995.
def localCycle00042 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 0 1]
    constant := ![0, 0, -1, 0, -1, -1, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, true, true, false] }
  origin := ![.triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 22 0, .triangle 23 0, .triangle 32 2, .gapUpper 3 3, .gapUpper 3 4, .triangle 1 0]

-- Original cycle a93444174c6a9b531e0f6f71bb0e108da6b80b3fcbb2f67547a537366d16bf26; original global index 13175.
def localCycle00043 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, 0, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true, true, true, false] }
  origin := ![.triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 2, .gapUpper 3 3, .gapUpper 3 4, .triangle 1 0]

-- Original cycle ad67da3a1a7f69fb84c883d99fd65fd540c5d55c86b1aa4370d3834f015efa3d; original global index 13526.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4]

-- Original cycle b21e1b52e7d1ca1f8227dcd40a0d01422ea55c3562b634f38501ed206071eb64; original global index 13918.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle b32355a7bda5eba509e8e438441ac110c2cbfc9a02c9fa05dac51e1256ee79d6; original global index 13999.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 30 1, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle b5a6bca4604299d452992faca652a8f55cb1d0406326c6095ee766633ad6faca; original global index 14193.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle bb3c2b7ac30ab48ad17854c0db497d5170a0dec4adc18b5a7f366c0d2eedb60c; original global index 14620.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle bbdd2769a76e7bdc61bda66392386acf6ef3bba98de1210ccb8acb5d4ca64832; original global index 14674.
def localCycle00049 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle bbf2943118912af9090b872909afb2e96291a8a77e4d7aa9c2a1b039fc021899; original global index 14677.
def localCycle00050 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle bc176c31608d148ae9214f083e162f0bb8e7bcdbc5bef8ed01c653aebd5d12ee; original global index 14685.
def localCycle00051 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 32 0, .gapLower 3 0]

-- Original cycle c09d786db3d29258f6a105ece81b7a8bd28f7ee77091152f76ed11de12fa698a; original global index 15040.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle c3ec34a7251672b9c07f463cdea53b742751d1741b529bd5e96912f22c6030f0; original global index 15282.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 22 0, .triangle 23 0, .triangle 32 0, .gapLower 3 0]

-- Original cycle c913cb2cc617611a0280012a5d1cf246cb2e5a22eb22d8e1730b3e2c8853d341; original global index 15707.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle cb547a1181aec8b3b5687bb4c2af42fe2a95fea943a1d4b67e578fac342b54be; original global index 15883.
def localCycle00055 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 19 1, .corridorLower 3 4]

-- Original cycle cd8a34640786866f0329868b75cf36aa507b34de4cd28fef1dfdc8ed27f16f14; original global index 16062.
def localCycle00056 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle dd1a62b7d6cc5a7e4a0bd44183d5331179723cdfaa336875bf5867ac9c5d0131; original global index 17285.
def localCycle00057 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 30 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle ddcd70fe1742a4a46fc1b40621977e21420916f6d5f3a686eec7b1b84aaac185; original global index 17339.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle de335373d6bdf8a1040092629cfa46002ac0dac5ee87e59d3a6681130ca5f8ab; original global index 17375.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 30 1, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle df356c46f12cca8895956d5c97d6f7fafb3aca103cee40981ec64068616ce82a; original global index 17445.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .triangle 32 2, .gapLower 3 0]

-- Original cycle e37e0e990000422abe25b5344fefe385930a32f2bfb8c01cd61d20b896cb0116; original global index 17791.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 6, .distance 0 3, .distance 1 3, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true, true, false] }
  origin := ![.triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 29 1, .triangle 32 2, .gapUpper 3 3, .gapUpper 3 4, .triangle 1 0]

-- Original cycle e56db9da1f4407c937f7c8da86c9494f7d007eafae5fabafca694bd45394f8b4; original global index 17940.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 3 6]

-- Original cycle e792dca0abd0987cfbd10ab732a3c49f7ed4312e8e816e57e4215e711b377486; original global index 18109.
def localCycle00063 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 28 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle f6bec516ca7e6990bd4053a3f947566c5ced5a13bdbd978605f9583fdedc869d; original global index 19251.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4]

-- Original cycle f75710e212d10b6a579df0afe9917ff55b48a8c4d93a2033db3020380de667e0; original global index 19293.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 29 1, .triangle 23 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle fa056e436508b9687b7e03e2ba452106c72a44b151bb95bdb1b44e6405bbd248; original global index 19495.
def localCycle00066 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle fc1662593c4cb8aac8962bea34e166eac64d5dd741a2b3b561a401e4412faa65; original global index 19685.
def localCycle00067 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .corridorLower 3 4]

-- Original cycle ff3e12838f2e7adc1611643ed0af3c3a3b6aad1c82f6f31ac139d91407c1635b; original global index 19954.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 7 0, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4]

def library : Library := fun id => if id < 34 then (if id < 17 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))))) else (if id < 25 then (if id < 21 then (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))) else (if id < 29 then (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none))) else (if id < 31 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))))))) else (if id < 51 then (if id < 42 then (if id < 38 then (if id < 36 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none)))) else (if id < 46 then (if id < 44 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none)) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none)))))) else (if id < 60 then (if id < 55 then (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))))) else (if id < 64 then (if id < 62 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none)) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 6, 4, 5, 0, 3], ![1, 6, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 1, 5, 0, 2], ![6, 3, 1, 4, 0, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 41 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14080)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 4, 5, 0, 3], ![6, 1, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 1, 5, 0, 2], ![3, 6, 1, 4, 0, 2], ![3, 5, 4, 2, 1, 0]], proof := .tail 27 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14081)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 4, 5, 0, 3], ![6, 1, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 1, 5, 0, 2], ![6, 3, 1, 4, 0, 2], ![5, 3, 4, 2, 1, 0]], proof := .tail 51 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14082)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 4, 5, 0, 3], ![6, 1, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 1, 5, 0, 2], ![6, 3, 1, 4, 0, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 34 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14083)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 0, 5, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14084)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 12 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14085)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 8 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14086)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 66 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14087)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 22 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14088)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 22 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14089)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 22 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14090)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 5, 4, 1, 6, 3], ![2, 5, 4, 0, 6, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 22 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14091)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 5, 4, 1, 6, 3], ![2, 5, 4, 0, 6, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 22 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14092)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 5, 4, 1, 6, 3], ![2, 5, 4, 0, 6, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 22 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14093)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 5, 4, 6, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 5, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 30 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14094)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 5, 4, 6, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 2, 6], ![3, 1, 0, 4, 2, 5]], proof := .tail 30 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14095)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 5, 4, 6, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 0, 6, 2], ![3, 1, 0, 4, 5, 2]], proof := .tail 30 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14096)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 5, 6, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 0, 2, 6], ![3, 1, 4, 0, 2, 5]], proof := .tail 20 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14097)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 5, 6, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 0, 6, 2], ![3, 1, 4, 0, 5, 2]], proof := .tail 20 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14098)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 6, 0, 2], ![3, 1, 4, 5, 0, 2]], proof := .tail 33 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14099)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 5, 6, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 0, 5, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 64 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14100)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 5, 6, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 0, 6, 2], ![3, 4, 1, 0, 5, 2]], proof := .tail 64 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14101)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 6, 0, 2], ![3, 4, 1, 5, 0, 2]], proof := .tail 45 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14102)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 6, 1, 0, 2], ![3, 4, 5, 1, 0, 2]], proof := .tail 31 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14103)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![3, 6, 4, 1, 0, 2], ![3, 5, 4, 1, 0, 2]], proof := .tail 10 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14104)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![6, 3, 4, 1, 0, 2], ![5, 3, 4, 1, 0, 2]], proof := .tail 22 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14105)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 1, 0, 2], ![6, 3, 4, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 60 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14106)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 6, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 6, 0, 2], ![3, 1, 4, 5, 2, 0]], proof := .tail 57 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14107)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 6, 0, 2], ![3, 4, 1, 5, 2, 0]], proof := .tail 59 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14108)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 6, 1, 0, 2], ![3, 4, 5, 1, 2, 0]], proof := .tail 31 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14109)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![3, 6, 4, 1, 0, 2], ![3, 5, 4, 1, 2, 0]], proof := .tail 10 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14110)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![6, 3, 4, 1, 0, 2], ![5, 3, 4, 1, 2, 0]], proof := .tail 22 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14111)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 1, 0, 2], ![6, 3, 4, 1, 0, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 60 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14112)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 6, 1, 0, 2], ![3, 4, 5, 2, 1, 0]], proof := .tail 46 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14113)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 0, 5, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![3, 6, 4, 1, 0, 2], ![3, 5, 4, 2, 1, 0]], proof := .tail 10 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14114)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 0, 5, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![6, 3, 4, 1, 0, 2], ![5, 3, 4, 2, 1, 0]], proof := .tail 38 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14115)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 0, 5, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 1, 0, 2], ![6, 3, 4, 1, 0, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 60 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14116)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 0, 5, 4, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 29 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14117)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 0, 5, 4, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 9 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14118)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 0, 5, 6, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 21 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14119)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 0, 6, 5, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 6 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14120)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 6, 3], ![1, 0, 5, 4, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 23 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14121)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 6, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 2, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 23 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14122)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 5, 4, 1, 3, 6], ![2, 5, 4, 0, 6, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 23 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14123)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 5, 4, 1, 6, 3], ![2, 5, 4, 0, 6, 3], ![1, 0, 5, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 23 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14124)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 5, 4, 1, 6, 3], ![2, 5, 4, 0, 6, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 54 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14125)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 5, 4, 1, 6, 3], ![2, 5, 4, 0, 6, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 36 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14126)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 5, 4, 6, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 5, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 48 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14127)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 5, 4, 6, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 2, 6], ![3, 1, 0, 4, 2, 5]], proof := .tail 48 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14128)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 5, 4, 6, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 6, 2], ![3, 1, 0, 4, 5, 2]], proof := .tail 48 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14129)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 5, 6, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 0, 2, 6], ![3, 1, 4, 0, 2, 5]], proof := .tail 55 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14130)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 5, 6, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 0, 6, 2], ![3, 1, 4, 0, 5, 2]], proof := .tail 55 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14131)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 6, 0, 2], ![3, 1, 4, 5, 0, 2]], proof := .tail 24 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14132)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 5, 6, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 58 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14133)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 5, 6, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 0, 6, 2], ![3, 4, 1, 0, 5, 2]], proof := .tail 58 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14134)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 6, 0, 2], ![3, 4, 1, 5, 0, 2]], proof := .tail 58 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14135)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 6, 1, 0, 2], ![3, 4, 5, 1, 0, 2]], proof := .tail 15 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14136)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 5, 6, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 0, 5, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 40 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14137)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 5, 6, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .tail 40 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14138)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 24 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14139)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 15 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14140)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 39 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14141)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 6, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 1, 0, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 0 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14142)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 6, 0, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 6, 0, 2], ![4, 3, 1, 6, 0, 2], ![3, 1, 4, 5, 2, 0]], proof := .tail 17 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14143)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 1, 6, 0, 2], ![3, 4, 1, 5, 2, 0]], proof := .tail 58 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14144)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 2, 0]], proof := .tail 47 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14145)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 6, 1, 0, 2], ![3, 4, 5, 1, 2, 0]], proof := .tail 15 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14146)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 2, 0]], proof := .tail 15 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14147)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 39 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14148)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 1, 0, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 0 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14149)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 0, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 1, 0, 2], ![4, 3, 6, 1, 0, 2], ![3, 4, 5, 2, 1, 0]], proof := .tail 4 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14150)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 0, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 13 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14151)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 1, 0, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 1 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14152)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 2, 5, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 1, 0, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 19 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14153)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 4, 5, 0, 3, 6], ![1, 5, 0, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 1, 5, 0, 2, 6], ![3, 1, 4, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14154)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 4, 5, 0, 3, 6], ![1, 5, 0, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 1, 5, 0, 2, 6], ![3, 1, 4, 2, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 63 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14155)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 4, 5, 0, 6, 3], ![1, 5, 0, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 1, 5, 0, 2, 6], ![3, 1, 4, 2, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 3 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14156)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 2, 4, 1, 6, 3], ![2, 4, 5, 0, 6, 3], ![1, 5, 0, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 5, 0, 2, 6], ![3, 1, 4, 2, 0, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 3 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14157)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 4, 5, 0, 3, 6], ![1, 5, 0, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 1, 5, 0, 6, 2], ![3, 1, 4, 2, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 50 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14158)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 4, 5, 0, 6, 3], ![1, 5, 0, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 1, 5, 0, 6, 2], ![3, 1, 4, 2, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 49 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14159)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 2, 4, 1, 6, 3], ![2, 4, 5, 0, 6, 3], ![1, 5, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 5, 0, 6, 2], ![3, 1, 4, 2, 0, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 49 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14160)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 2, 4, 6, 1, 3], ![2, 4, 5, 6, 0, 3], ![1, 5, 0, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 5, 0, 2, 6], ![3, 1, 4, 2, 0, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 3 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14161)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 2, 4, 6, 1, 3], ![2, 4, 5, 6, 0, 3], ![1, 5, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 5, 0, 6, 2], ![3, 1, 4, 2, 0, 6], ![3, 1, 0, 4, 2, 5]], proof := .tail 49 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14162)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![2, 4, 5, 6, 0, 3], ![1, 5, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 5, 6, 0, 2], ![3, 1, 4, 2, 0, 6], ![3, 1, 4, 0, 2, 5]], proof := .tail 14 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14163)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![2, 4, 5, 6, 0, 3], ![1, 5, 6, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 5, 6, 0, 2], ![3, 1, 4, 2, 0, 6], ![3, 1, 4, 2, 0, 5]], proof := .tail 5 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14164)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 4, 5, 6, 0, 3], ![1, 5, 6, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 5, 6, 0, 2], ![3, 1, 4, 2, 6, 0], ![3, 1, 4, 2, 5, 0]], proof := .tail 16 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14165)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 4, 5, 6, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 5, 6, 0, 2], ![3, 1, 4, 6, 2, 0], ![3, 1, 4, 5, 2, 0]], proof := .tail 28 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14166)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 4, 5, 6, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 6, 5, 0, 2], ![3, 1, 6, 4, 2, 0], ![3, 1, 5, 4, 2, 0]], proof := .tail 44 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14167)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 4, 6, 5, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 1, 6, 5, 0, 2], ![3, 6, 1, 4, 2, 0], ![3, 5, 1, 4, 2, 0]], proof := .tail 11 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14168)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 4, 6, 5, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 1, 6, 5, 0, 2], ![6, 3, 1, 4, 2, 0], ![5, 3, 1, 4, 2, 0]], proof := .tail 32 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14169)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 4, 5, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 1, 5, 0, 2], ![3, 6, 1, 4, 2, 0], ![3, 5, 4, 1, 2, 0]], proof := .tail 42 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14170)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 4, 5, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 1, 5, 0, 2], ![6, 3, 1, 4, 2, 0], ![5, 3, 4, 1, 2, 0]], proof := .tail 53 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14171)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 4, 5, 0, 3], ![1, 6, 5, 0, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 1, 5, 0, 2], ![6, 3, 1, 4, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 26 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14172)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 4, 5, 0, 3], ![6, 1, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 1, 5, 0, 2], ![3, 6, 1, 4, 2, 0], ![3, 5, 4, 2, 1, 0]], proof := .tail 61 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14173)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 4, 5, 0, 3], ![6, 1, 5, 0, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 1, 5, 0, 2], ![6, 3, 1, 4, 2, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 25 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14174)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 4, 5, 0, 3], ![6, 1, 5, 0, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 1, 5, 0, 2], ![6, 3, 1, 4, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 62 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14175)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 5, 0, 4, 3, 6], ![4, 5, 0, 1, 2, 6], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 67 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14176)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 5, 0, 4, 6, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 2, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 12 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14177)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 5, 4, 0, 6, 3], ![1, 5, 0, 4, 6, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 2, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 22 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14178)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![5, 2, 4, 1, 6, 3], ![2, 5, 4, 0, 6, 3], ![1, 5, 0, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 2, 0, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 22 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14179)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 5, 0, 6, 4, 3], ![4, 5, 0, 1, 6, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 2, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 8 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14180)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 5, 4, 0, 6, 3], ![1, 5, 0, 6, 4, 3], ![4, 5, 0, 6, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 2, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 22 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14181)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![5, 2, 4, 1, 6, 3], ![2, 5, 4, 0, 6, 3], ![1, 5, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 2, 0, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 22 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14182)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![5, 2, 4, 6, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 5, 0, 4, 6, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 2, 6], ![3, 4, 1, 2, 0, 6], ![3, 1, 0, 2, 4, 5]], proof := .tail 30 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14183)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![5, 2, 4, 6, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 5, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 0, 6, 2], ![3, 4, 1, 2, 0, 6], ![3, 1, 0, 4, 2, 5]], proof := .tail 30 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14184)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 5, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 2, 0, 6], ![3, 1, 4, 0, 2, 5]], proof := .tail 20 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14185)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![5, 2, 6, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 5, 0, 6, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 2, 0, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 64 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14186)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 5, 6, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 2, 0, 6], ![3, 1, 4, 2, 0, 5]], proof := .tail 65 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14187)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 5, 6, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 2, 6, 0], ![3, 1, 4, 2, 5, 0]], proof := .tail 56 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14188)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 5, 4, 6, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 1, 6, 0, 2], ![3, 4, 1, 6, 2, 0], ![3, 1, 4, 5, 2, 0]], proof := .tail 28 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14189)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![5, 6, 2, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 5, 6, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 2, 0, 6], ![3, 4, 1, 2, 0, 5]], proof := .tail 64 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14190)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 5, 6, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 2, 6, 0], ![3, 4, 1, 2, 5, 0]], proof := .tail 52 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14191)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 5, 6, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 1, 6, 2, 0], ![3, 4, 1, 5, 2, 0]], proof := .tail 68 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14192)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 6, 1, 2, 0], ![3, 4, 5, 1, 2, 0]], proof := .tail 35 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14193)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![3, 6, 4, 1, 2, 0], ![3, 5, 4, 1, 2, 0]], proof := .tail 10 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14194)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![6, 3, 4, 1, 2, 0], ![5, 3, 4, 1, 2, 0]], proof := .tail 22 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14195)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![2, 6, 5, 4, 0, 3], ![1, 6, 5, 0, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 1, 0, 2], ![6, 3, 4, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 60 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14196)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 5, 6, 1, 0, 2], ![3, 4, 6, 1, 2, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 43 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14197)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 5, 0, 4, 3], ![4, 5, 6, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![3, 6, 4, 1, 2, 0], ![3, 5, 4, 2, 1, 0]], proof := .tail 61 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14198)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 5, 0, 4, 3], ![4, 6, 5, 0, 1, 2], ![3, 6, 5, 1, 0, 2], ![6, 3, 4, 1, 2, 0], ![5, 3, 4, 2, 1, 0]], proof := .tail 25 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14199)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 5, 2, 4, 1, 3], ![6, 2, 5, 4, 0, 3], ![6, 1, 5, 0, 4, 3], ![6, 4, 5, 0, 1, 2], ![6, 3, 5, 1, 0, 2], ![6, 3, 4, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 2 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14200)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 5, 0, 4, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14201)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 5, 0, 4, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 9 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14202)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 5, 4, 0, 6, 3], ![1, 5, 0, 4, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 23 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14203)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![5, 2, 4, 1, 6, 3], ![2, 5, 4, 0, 6, 3], ![1, 5, 0, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 2, 6], ![4, 3, 1, 2, 0, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 7 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14204)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 5, 4, 0, 3, 6], ![1, 5, 0, 6, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 21 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14205)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![5, 2, 4, 1, 3, 6], ![2, 5, 4, 0, 6, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 2, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 23 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14206)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![5, 2, 4, 1, 6, 3], ![2, 5, 4, 0, 6, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 1, 0, 6, 2], ![4, 3, 1, 2, 0, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 18 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 14207)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (14080 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 14080 ≤ id.val) (hhigh : id.val < 14208) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 14080)) = true := by
  let j : Fin 128 := ⟨id.val - 14080, by omega⟩
  have hsum : 14080 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (14080 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard110
