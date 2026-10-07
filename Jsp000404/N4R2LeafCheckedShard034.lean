import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard034
open N4R2RowDataReplay

-- Original cycle 007a260d80f791b6d423868080b80a2adfc9ca2cb489ef6aee87adb0b9251f27; original global index 42.
def localCycle00000 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 0 2, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 015aa5559483cb18281693b130013907c946c2c1e80d843c5ff390056a3d691f; original global index 114.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -3, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 01fa8770976bf7257a8be6343f0a50c408ba8fd1f25c9681d2cfc30314aa555d; original global index 157.
def localCycle00002 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 028ac5a9078985b7628e87d98b9551b560595af7236971b85f8aa148816d1462; original global index 198.
def localCycle00003 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 031aa33f5ab8d4436e30a71abb2765b44b6b4fcb6728be66dc34f53ddc5e4230; original global index 253.
def localCycle00004 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -3, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Original cycle 0345b2e64f6c77c5320d62448b0b0854a0373dc99afd5058c5e2fa94e6c49efa; original global index 263.
def localCycle00005 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0358d358b0629715cfeb81d59fc3a2620fcf4bc83e5888ef55b51d67b8dcd169; original global index 271.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 0420c1f04bf85a5258365f5c40fe78bf45b2092b039c18cec750b1f92a177f69; original global index 324.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 045177addd8632b6124533fe8877185d39e178582f6b5af61a0fece59458aad1; original global index 341.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0451dbd8f382534b6827c272d2fc88f718354ea99e7ce11223f4207ff7a46867; original global index 342.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 04c930e477bbf32291c5fead18c0529fc02ba8a488757fb325042c1176c8e307; original global index 385.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 054dd864edae0bc915fbda2c2dc9db2baaa24d01aca43baf35d225a28a60b307; original global index 428.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 05c5388c352a45349c8afd7746110e56fba2b84f3ca845c1c711f7aaa05d6667; original global index 479.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .triangle 29 1, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 06ac7cb80423cf9ed5fed2ff6f3a83582e7d1b8dafc2f9111072b3a32fcacb66; original global index 549.
def localCycle00013 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 6, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 2, .gapLower 6 2, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0720ebaa2e5c908014a8a7432b84a933e6f8c24ef0c855112d54e61078b2427c; original global index 588.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 07e07c900646a2bc8a3d0495af20dff46f0b701dae8bae333cd309f87a74bf48; original global index 636.
def localCycle00015 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 07e16562c03d5f577e3b6f20f936a222613d6e92cb97616f7c90dfba5e5a4a3b; original global index 638.
def localCycle00016 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 087b25105d8338d378c8fde0e5aa36588793ac3a4759ab4b56439a386f1b4b8e; original global index 677.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 23 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 09557cc1b93858f856f165d0f8859e670a4f5557edb70d446a5330aa588f8303; original global index 743.
def localCycle00018 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 099b6a998fdac81e716c624fab1d037d9a9ec641a968c2b0100d58d9cee22aea; original global index 764.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 09b8fc03ba94c589fa64d801cb44108d2bc7b63b15254b331107b172c55aeca0; original global index 777.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapLower 6 2, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 0b0db714e21763fcf9c35c8d88054b67b078617575778a5800165f342462de51; original global index 884.
def localCycle00021 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 0b273fa4d5fe511058574e9e3a1a0a385b0c4a6dcaede7425588e2adcb855547; original global index 892.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 6 2, .triangle 13 2, .gapLower 6 0]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00023 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0e41968f8599f9e965b7970f0fa6d82f81e3a1a9881f481498ba244d04635f58; original global index 1123.
def localCycle00024 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 23 0, .gapLower 1 3, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 0ec4e83fd5ce31c7b25da4a69acf0cf5659e146e33aba5733d871def85e6e1d1; original global index 1168.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 0ec9b4adead2924ffd2b4fc592ec1ff1acf25bf18ea05caa06bcc540c31a8000; original global index 1171.
def localCycle00026 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 0eefc427fed3fd526228d0454c2f0721fdeb27a60b77e105a5e2cf121e2a3531; original global index 1182.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Original cycle 0ffe38a2ff74353a6720ac5f780cf859cbffbac4d17c1227510a916080305dee; original global index 1277.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 10298c3d46d4c845297300c3746ac4007b8417e8992557fdc288f399c7c151c9; original global index 1299.
def localCycle00029 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, 0, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 108d98a917934b39fc7cbeccd36341e038ae4677cd88986a169b40bfb005a370; original global index 1327.
def localCycle00030 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 2, .gapUpper 4 3]

-- Original cycle 12a7c3180ef18564b0d61d99e5619e897643776f0f12042e0c781413781b0bde; original global index 1474.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 152486ab0b1a353b34cf7dd48121623c50abd5aba4a5434328725d63d6f0a00d; original global index 1673.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 23 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 156b777143e47af89725913aaccc1759e20ee561de4259c78bbed3f3d93f30cb; original global index 1696.
def localCycle00033 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle 15ec34fd637924c166ad72aea0e192e55868596237a939d3bdc7cd27687a856d; original global index 1738.
def localCycle00034 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 2, .triangle 16 0, .triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 173fd02ab225acd6db5b51a1df1b9e94daad18b1427ddbbdd9a71b0a65d78a77; original global index 1828.
def localCycle00035 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 23 1, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 17c4bda79330dff4f33f70f264fb905fd649dd567bb44437df46d7836db97937; original global index 1857.
def localCycle00036 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 4, .triangle 15 2, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 18e075ba27c4302586949da6184a37478aea6bac1d485f4d96b55f0338d608fd; original global index 1944.
def localCycle00037 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -3, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1c9af3b01e50b8762994099a8830002b52136f56490a0f53b05b5e159fa515df; original global index 2202.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, 0, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 32 2, .triangle 27 2, .triangle 18 2, .triangle 4 2, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 1ccc05e4d7581b492c9dfd4c8045e4a666ca9824b65b6c17654972d9c19a318c; original global index 2214.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 2, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 1ddc1fa9c7b1fc507998ed27d09e8f91212ca6cd3375b7b0bcaaa04d24bbf827; original global index 2293.
def localCycle00040 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 1ddf19a39a831bc3bfa6551ce4c9d9660b796a44e69d300496835e11cf9d66ec; original global index 2294.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 30 1, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 1e2e73cbe1703fc53c1b73ada82522139d8913e8cea44f1aed24fe8d049163f7; original global index 2321.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 29 1, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 1ed4fef1dd61731d4f30f80bf3d9c08a2758c524d15de8d2c14adcde069f3d20; original global index 2366.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 30 0, .corridorLower 2 5]

-- Original cycle 1f80d5b15ad7b79e653b5cfc8a875a90612249225eb79872a53d5613a4afcd8e; original global index 2421.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 1fb149b17761516cf76b8b78058fbaa6ca68ff2d88bec88e7578a01bb69205cf; original global index 2439.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 13 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 209e9b52392668bb7e3dc70e9bb92d59fc51e5a5c389ec68756a2ceaffe5d05d; original global index 2502.
def localCycle00046 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 217a0f61d52c3f896343f31e37cb1da1a7013a700049c8156dd517450dbf7de7; original global index 2563.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 219679b9d7a70286490a793b4bf0ffc52b2197c7779ad45e8b39ac82d0ae0483; original global index 2570.
def localCycle00048 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 227f6a493c616b231f78ecc2b6fac89880ba8c4142ef628dace8663a3a4715c1; original global index 2640.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2355b06a170485b0bd8d19eb36da8e614b3e1527539bf92a4504aa2dc91d2043; original global index 2707.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 258721d0d59ef7a4da486fe731cd979328d5f81e30ddc469e74610d10514efb8; original global index 2884.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 8 2, .triangle 13 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 289870e23750518284c531a58074274f287227795f61e1726d2d647808b0791c; original global index 3107.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 2958fb68c875ad3854699bdb4e1a014a9915ca8a8d6a576cf8d831eedce3f2b6; original global index 3155.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 29757fba9877caa461692688935dd74a3308bf6277d611e5ce05b0d13c348125; original global index 3161.
def localCycle00054 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 32 2, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 2988058a721ec1aca6ca99e99b5b4e1b273214c18447f956cf9efa53d8372dc6; original global index 3166.
def localCycle00055 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 2a4c180de0975322573cb7d46f544e8f9038771af6a2e14287f3fa34fc045e78; original global index 3223.
def localCycle00056 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, 0, -1, 0, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 25 2, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 2ad1d1306ca60c24e3525d2596ee053496c66047f4b625a9756d5cbfd98ef5ff; original global index 3264.
def localCycle00057 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 4, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2bf7bde31b897f57fa851024aa241fc773da8bfd475540c9d01ca00523a09be9; original global index 3362.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2c8feb11536489c75b2c728c8b3e36d0c3151e0992f6b55aff6619331525bd65; original global index 3404.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2]

-- Original cycle 2cfc292e4a6fc6cad45946cfade48c12ef6a086feb597f24e738102e374d7d79; original global index 3437.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 2d080be512d8d23db6205a7cb89eb007ab01be83b366d58b74d77ac44af54038; original global index 3439.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 2f4890359cea41721f0c336c69c7360046e021e1d22bd3b00b8500e5548788b2; original global index 3614.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 3, .triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2fc1b4a3f9d08a48e838a1ff2b76bf76ee34287e820acb5c7973cca3cf837606; original global index 3651.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 33 0, .corridorLower 3 5, .thetaNext 2]

-- Original cycle 2fd1237237dbf9a2049b30a44b22779a427557ae7ccaf754ea3144ef8c4c928c; original global index 3654.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 30e6ce3a7a0bad9350fc1fd4f0ed82642044bdc0d0d27d84955bb60bc269c0b7; original global index 3729.
def localCycle00065 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 21 1]

-- Original cycle 3376642a96131b9eeacd645104478b0d06b24e6cd9a6624bcaf042eb97c0c52d; original global index 3937.
def localCycle00066 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 3401a4ac5f2e87583f544ae5a48964f6f6bbbf6aba082b0bc7f841afe5b95cef; original global index 3983.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 348bfe2a457ddeab530f0a8428aa5dbdd7c95377ce9005363654f00540581a11; original global index 4022.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 35bd590375bb7a012997f5f610269f6f8fd42aff0cd82fddfb27724a25b14038; original global index 4118.
def localCycle00069 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 368df2626ca45afa1a79b8eae932b2ba95e23423dce56dea6e2b868298b9f46d; original global index 4190.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 389491ec4695415f7a1b93d460cb3076354d29a66da124b21d2a468fefdf08a4; original global index 4353.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 38d168c1216f6824a2a3a4f5344aa5e0cfe72be2d0ddcbd3d51dda54d5b4aafe; original global index 4374.
def localCycle00072 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 4, .gapLower 2 3, .triangle 5 2, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3abb17efa5f68184bd3773cc805dff24e9ff8c9ec11984322766fbd077569ee9; original global index 4534.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3b113b81d344803e9a91f2db742a3f5318397baf8a1c2ec691fcd22948252e15; original global index 4565.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle 3c38cb35a01a0dff849bd22050749eb8e1fd755a41bc45ae0ea5b204feeaeb7d; original global index 4670.
def localCycle00075 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .triangle 23 1, .triangle 34 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 3c5a808dc935969693c4424bef426424a1f3c10e9b1f758fae850d0a8b047766; original global index 4679.
def localCycle00076 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .corridorLower 4 6]

-- Original cycle 3e2ca9029fa75977f39d73ab03058afbbb372e4b6e4ec4dd1b1e19717c06b4cb; original global index 4810.
def localCycle00077 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 3fa88d906305ebd56cececabe025a262190baa06835cf4de2eecd6de0477e535; original global index 4915.
def localCycle00078 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .triangle 23 1, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 402420e40fb777df51bc87862733e8a9c6938e96d3f8a95a4e6fe836f8a10da0; original global index 4950.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 40ac7453c8a465d646d441af02b925c6e570d4e91e0d5a8e77fcdc4d09083fe8; original global index 4997.
def localCycle00080 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .triangle 18 0]

-- Original cycle 4266614f088427d2b310ee8dd047b93443adb68d18d6e0a7e145e2accabdea64; original global index 5115.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 42c587fb0563569c711cffd5356d5cf61c6e5d11b669293960d02ec5866613ec; original global index 5143.
def localCycle00082 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 434a64d094f75fcaadf6ed097c05d7e3cd8e33b1cb0ed606f0f2bef8cc7b87a1; original global index 5195.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 23 1, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 44549c54acd8bc9b0ae240633fc166192ae8f988b58868273e99a0eec8072fb6; original global index 5290.
def localCycle00084 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 452a47ad1eaed52a29541673c9edd208a3a137a7ea83002d4d835e7f1df390ac; original global index 5350.
def localCycle00085 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 45fec23e2594154e179ed50fd7dc72c3f7d5ee1a781d84cbe13ad41f7c3d823b; original global index 5416.
def localCycle00086 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 47c53fad7653dcf286669560b5ef3561500b7ff9ddfb709b8fe3682b6de8a668; original global index 5561.
def localCycle00087 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 0 6, .distance 0 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 6 2, .triangle 13 1]

-- Original cycle 47de3e91fd6d50cb8e34a7dc32db523f10047e6e1e8689d9dedb54522ec7260e; original global index 5563.
def localCycle00088 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 487322aa05a134fd63b0520f4d846ea5686afa6b08727a5160a82c916be7a75e; original global index 5613.
def localCycle00089 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 499049b8cfefff6e18df513fda6da8aecb9ae7a4333fe23f85b72bb69ef6384a; original global index 5706.
def localCycle00090 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 27 1, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 4b955f9242a107c9df2c9fee3ba6a59587d132edc29d6be8bf01eacaee488d8c; original global index 5864.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .triangle 18 2, .gapLower 6 3, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 4c935301f2212f3cedc07789e18e15e5415b8dc4fd5c905fdbc4152616ec8bce; original global index 5944.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 2, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 4d506e39a0e7c7916f8af4d55c306c2639e7378041917ea7cbca7d03037b1adc; original global index 6004.
def localCycle00093 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Original cycle 4d86bda4b79ec46f2270b5e15255f3ceb6eade89bc1747c3891a0f3e9754dc10; original global index 6020.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .gapLower 6 3, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 4f4bdac3d30751954c3a68d50a85fbd3ef53769b2dfe3795d2c1d5a41f9c34fa; original global index 6163.
def localCycle00095 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00096 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 4feb53fd0e6d01f3cb838a51a777001988aad8f3d219ff27d920e5623a20f4c3; original global index 6203.
def localCycle00097 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 50f490d2f9e63725084a6a200390e4666ce652857abc8c5608e2bdf724d9048e; original global index 6288.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 24 2, .gapLower 6 2, .triangle 34 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 51cf2e8b74d3a16839eb71339ee0b0dde5cd753f2ab0146db62709e76adf6202; original global index 6364.
def localCycle00099 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 53c721eb75905d2a7257424e67287889fc066fd804e12d91258bf924026801e9; original global index 6506.
def localCycle00100 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 53f632116fb63e8837f13ade08f6ff477c35fde887ce06fad4e7530e6341fd3f; original global index 6514.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 5575eeb5c7cbf4a6c8bc4684bd448893db601748b1897d0369b661c2681adb0e; original global index 6619.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 23 0, .triangle 29 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 57a35eef8c1e1c61d2e2b07ca48642bb55a7ff9b2e267e651ab4c953b504932a; original global index 6804.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 3, .triangle 13 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 5849d2324ee0005b831208a5189040019b54eacabc3989d1baa7bbc62638fd75; original global index 6850.
def localCycle00104 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .distance 1 3]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 3 3, .gapLower 6 5, .triangle 29 1, .gapLower 6 3, .triangle 21 1]

-- Original cycle 58ca7ddf74feda1382c28f3c64ead32b2c125ddcea7ad0ce95d316b57a0741af; original global index 6887.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 592c979471e620bbcc5f695e3f0e20e413ab0beaf84c932976450b7ca132ace0; original global index 6916.
def localCycle00106 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6]

-- Original cycle 59f7e16cf0df19d2f5b95699c9f9b78d8e450d0b809aafc2f34e88734ce0e76e; original global index 7004.
def localCycle00107 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 5acda26beb4a101904bdb5f433bfe3076301c7db29dcdd1a47a5fd0abaadabdf; original global index 7071.
def localCycle00108 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6]

-- Original cycle 5b6f2332d13581bc7c857b32bfa23bbaad43bc84d9c747eeec8dea66b73b503c; original global index 7115.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 27 2, .gapLower 6 4, .triangle 23 1, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5cd61694f127c91fed896dec404671b9d1eeba015dbeff17de906b69cd8da802; original global index 7225.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 5dda3bd582d7d0119b81fe42c057171d974b6cb4eba47e2c0ee832bfd73e2213; original global index 7300.
def localCycle00111 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 22 0, .triangle 23 2, .gapLower 6 3, .gapLower 6 2, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 5e9d348df1212f9d94801397a756b9e8e43fc62f0e6243bc876b988d9856a847; original global index 7357.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 5ef377858d02d40ff409ea3cbd97db1dbe84a54d2a1a02a1607b95a0c99483e2; original global index 7391.
def localCycle00113 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 1, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 61c013adcbbdcaa017c9de286a13ddb959bb98ee90330ed2758acfa446eed26e; original global index 7629.
def localCycle00114 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 627fc1115bda8b9263b9efbe9b9c7be80ede93ca129b664fdbf9712ce5fb6266; original global index 7685.
def localCycle00115 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![0, 2, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapLower 6 5, .gapLower 6 4, .triangle 23 0, .gapLower 1 3]

-- Original cycle 65f25373e1fed04fee94e35a36ebcf95ee34ef00101546076719904ee06a5fc5; original global index 7933.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 2 6, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 672189a913a93b0cc04ff18b6a9a5bce09baf9eaed75513840bff56e57da4e23; original global index 8018.
def localCycle00117 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 67a5f6ed7961aca4e77992957f5b6afdd333d8114169360faf1dab52ef9ff4ee; original global index 8051.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 3 5, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 6 3, .triangle 13 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 6aaf62f73fb3803c50ba13662ed0232aa10eec240f68c2a7c1e7c1e3016d2d76; original global index 8306.
def localCycle00119 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 24 0, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 6cc79ff8217f855ef7d7361d888290ee19eeb59f8a1dfee62b01efa3e20e05df; original global index 8465.
def localCycle00120 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 6, .distance 3 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 8 0, .triangle 27 1, .triangle 32 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 6f9bc61dc527802f84d235ff4658f7226ea610fcaa19a701f52cdde0f55e24cc; original global index 8657.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 2, .gapLower 6 3, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 709ada22d1475bd6a358979359357b87706e52b41023d1b693c316d56a3fd4ab; original global index 8724.
def localCycle00122 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 2, .gapLower 6 4, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 70ee133ced1ef1e964c8afa99aae874ab41f497f012fbd9ed6648b1bee86edda; original global index 8754.
def localCycle00123 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, 0, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 7234a882c37da328203c7260b33196fa9790dbc9f8b45275144647968f5b343f; original global index 8854.
def localCycle00124 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 2, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 726cf1bb095d391107264444fb8c65fb9a229f4a6dd184f83c4ba84d066832b8; original global index 8868.
def localCycle00125 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 4, .gapLower 1 3, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7281b2e6a2bf6db9d997cdb5b1bcab3c83ae5aa3ac1955f9e8c4f9c7caeeefa1; original global index 8872.
def localCycle00126 : Cycle where
  length := 6
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6]
    constant := ![3, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 0]

-- Original cycle 729711b4fa7ac710966d7b8847b74268e45e3b8508e40362ef87c17127911061; original global index 8876.
def localCycle00127 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 73640f4d1d257778a36698b59588aabd92676da54bab8f76983d640cd5d8ba91; original global index 8939.
def localCycle00128 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 752fe3ec52d620a9420f76fcdcd3e129cc1853855fbae917388cb5d95d4a5e40; original global index 9080.
def localCycle00129 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 781a19779908b64430f3b8af9a20e62e2e1ce312014f0b859b691c589b501d67; original global index 9284.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 2, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 786f3d477577e1d75839f6020ac7f5f768e59aecb121ce3178fc2f19dc6bb113; original global index 9315.
def localCycle00131 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 12 0, .triangle 13 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 79d5ce7db1d08d13b91f426d57cbbfb55d15a619088ae4955c9fde5509f8e655; original global index 9423.
def localCycle00132 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .gapLower 6 2, .triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7a544d9bbb518c3a3a188602b96ab1a73429200465c9ecbcb98540c378a3b6af; original global index 9462.
def localCycle00133 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .gapLower 6 1, .triangle 8 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 7b4b5a5744bec63570309cfeac6e582994715d44087cc648ada96385dff27a96; original global index 9547.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 7b7faf316ac15257e0bc1520a192b509eb09e463307e743db4003400c6901d4f; original global index 9557.
def localCycle00135 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .gapLower 6 1, .corridorLower 5 6]

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

-- Original cycle 7c2f4c0d0bceaa13db709ced0e8218a65db7a7b9834a30f02720dde8b1303648; original global index 9610.
def localCycle00138 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 23 2, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 7c3165f21d5f9b305437f0c6e8d72023744a85404010633a05192a25acf89a91; original global index 9614.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 4 2, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 7c48b0ed5a5c3382906eb0d0499234b42daf2501c377144b5d3c76dd804a361d; original global index 9618.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 7cc5b77f7a37f9df1e0c248c48adda039326a8fc96cd6876375bd33cd98fb286; original global index 9665.
def localCycle00141 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 0, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 7f09d2f48272cd7b45e327e603136339f77d8dab9e9b3831470bea642c7b11ea; original global index 9859.
def localCycle00142 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 80274ee74d88fb7a879bc91ac0f033a7d496b22801dba99f846b2de6119e41c3; original global index 9942.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 805b8b6ae1757abe9d54f1a16f7c6cda92a05709b6f9804eca837860028650a4; original global index 9958.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 80760b7db5e2e59f8b4e43c9abc858cfd84c64a01bbb48fc289bf3dbcce80070; original global index 9966.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 2, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 80967549ac57e27f35b87052abe8364bcacb60ee1f1a9bb26a0736c24da76938; original global index 9981.
def localCycle00146 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 815029151330f4b3ccf646b35ca1b8333dc99f6a75093789ccfb46ad8747ccda; original global index 10040.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 827dd1db3d3071a2f82ec4c8e0cef557c2bb5cf7cd8497604be6f1a3995d270e; original global index 10125.
def localCycle00148 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8369fb6752243115fdfee71b0cf84f688866256cd314f757833f749cf88782a9; original global index 10193.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 83986cae57bdea91fdac6464e214d58b8896ee1bbd986d9ff1f66304b33eccfd; original global index 10216.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 14 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 83ee7aebddc7a9a8c775f7be41db7733b938bb778ebe0faed8fbf686e65ec113; original global index 10242.
def localCycle00151 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 23 0, .gapLower 1 3]

-- Original cycle 84d3cddb9791b73af95b3ebf8adbe688ebc1dab8c92379a17acd23635f2ea869; original global index 10316.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 23 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 86a19fb48bd52ec29b7abd823e159503b2c319514bd183ace76b1cee28489d3a; original global index 10439.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 30 0, .gapLower 2 4, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8705542bc734f2dd1164f06b4147dd6d14688501460772d3edb026b7b3b74785; original global index 10473.
def localCycle00154 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 23 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 878fb9efa742f9775c292f0f8f0aac146491a14d42f69dabd8f8f21ab970c725; original global index 10511.
def localCycle00155 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle 88040156c4778ef2c57ecfa8832a4545c3c8ee9fe7b581e7f1a61b008e278066; original global index 10544.
def localCycle00156 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 29 0, .triangle 32 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 894858103d57ed1590941959ce2da12c5266c94b29f2ac6710fbb69f3c369ffa; original global index 10624.
def localCycle00157 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 896741b77d7c0476aa3e9c2f6f06acab4f2f7b251f90955a584eb9eed2b052f0; original global index 10632.
def localCycle00158 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 2, .triangle 13 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 89f97a162a4bad6666e49b980f8d2fa049effa72a246a7955689123ad354398e; original global index 10693.
def localCycle00159 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 8a92f5c45d4a8c6bb537a7d43ac98b39fcd7be4267191bf1cac0554d73a5ec4a; original global index 10733.
def localCycle00160 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 4 6, .distance 1 6, .distance 1 2]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .gapLower 6 3, .triangle 18 1]

-- Original cycle 8c369ed5234554b3e7e46030adad0afc516db5304d58543099de0ea8e7c913a6; original global index 10851.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 8c4318eccd751cc88271752cee6de48a154a9aff8a26fe2ab30dcc87a8869621; original global index 10854.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 8ccf15c7da327f74cf28e24184f519d09f9b60274d7497726782555f97523ec4; original global index 10890.
def localCycle00163 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 17 2, .triangle 24 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 8da220dfcbe98febab67784c71b34f7b20a2d2e535d839d6a0c19b8e6baf54fe; original global index 10953.
def localCycle00164 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 8dcf6899888c0111b8be2e3ea4b25129955fd93935779fa12fac181b27bb595f; original global index 10975.
def localCycle00165 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 0 4, .distance 0 6, .distance 4 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 12 0, .triangle 13 2, .gapLower 6 2, .triangle 34 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 90db02fff53da3a1a27de01ed023112a294d8f4eba00cd11a721128d944e95e5; original global index 11216.
def localCycle00166 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 91d62c6b7d30de85c9833e0394a0cb82f9b7f1cc83be0f883c74a6f837afd4be; original global index 11301.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle 928713b3dc836dc5dd293e65cb7b13534b205c8de6bfdfb63fe0eee618161b61; original global index 11350.
def localCycle00168 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 4, .distance 0 6, .distance 4 6, .distance 0 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 13 2, .gapLower 6 2, .gapUpper 4 1]

-- Original cycle 92b610380811fc3f1bb141f4cbcad7384a3f9aee21f5587a4f90f32c94be5f24; original global index 11368.
def localCycle00169 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 930bf4b019ca510eabc27643050b5c653f2ac6cd49c1708285dd74b9573292e5; original global index 11401.
def localCycle00170 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 934384c63d0048d0991a412cf6d213de27a1ef772bc5ad213d78c5a7d29f1365; original global index 11420.
def localCycle00171 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![2, -3, -1, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, false] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 23 0, .gapLower 1 3]

-- Original cycle 9477f6806c7cc8956e5f7211cfe5bcfd42b18b5af9a378711216b1818f1efff0; original global index 11522.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle 947fc0c31207be64695927683671767575a5524825bff9e7a188cb7c43ca895f; original global index 11523.
def localCycle00173 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 95f65cf8f26099118e8bd237d72cd9ba06d656f9e67e569d5d18bc4d25f3f25e; original global index 11661.
def localCycle00174 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 961f335e053fcb7305a80e9057eaf4c93b1e99b282c4f44aa2b81df7cf313990; original global index 11671.
def localCycle00175 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 4, .gapLower 2 3, .triangle 5 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 962be0ddbfabae78350220dda2eaefeb07dc713f0793d5f4ae1536ccf8e34cb7; original global index 11676.
def localCycle00176 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapLower 6 4, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle 987737132558b9e2d58538752baeeae1cbe0a966749dbfd06c74dc00d5755b3d; original global index 11840.
def localCycle00177 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 28 1, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 98b58a8d7bbce0bfcaec8f8cf05f6ab20e00da73a60d95bee9bac2dfa8d1d8d2; original global index 11861.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 98e99ef1026f4e3aedccfeca264faf5a3b06eaeb23cc259dda0f83856e3396d2; original global index 11872.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 9ac7ee5e339a0352fed1abc310d693c612d7ac357fcf79d8cdab6544a0143a95; original global index 12029.
def localCycle00180 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle 9b6dea399498e339068ffe0dc1877c67844a54133cd675f630c9045d0928c192; original global index 12088.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 9c5eea598badabdb92f4cc49b6924cc81650e1e78eab3a7a14daadcf82810ce6; original global index 12164.
def localCycle00182 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 2, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 9d37351b1cc48efbe4f6675d4a689f9133cc5040db2ab4b7932e45b2d06e0fde; original global index 12232.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, 0, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 9e0c2a98295a93f8739900473ba6fd4258dc6cc14c1ed8ae5ec194455868a7c0; original global index 12298.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a1fe57f771416b7ffa9ae228487b313f78ae31303601ccc029a4ead805606111; original global index 12597.
def localCycle00185 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 14 1]

-- Original cycle a26ec7336222745d0d458c501c14f4f8251c84e1d0efdf6b7fb176364539fb96; original global index 12635.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle a3928ebf929ad770c76cb380eef19e770c638b3a1b1037db4aef5538e048be58; original global index 12710.
def localCycle00187 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle a509b6666f56dfe4a5291e535c666050ac0289bc576462aed20e7e11c2b32456; original global index 12827.
def localCycle00188 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -3, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle a7d1bf8c040f9b2c04b4cb7cd172a28a2cf2a74a8aa56e620ba9baaa292788de; original global index 13060.
def localCycle00189 : Cycle where
  length := 5
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 1, 0, -2, 0]
    coefficient := ![1, 1, 0, -1, 0]
    strict := ![false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 23 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle a9707215f99a8e69d5fcd6ef958d61def534f35a301e1e20c240afc21aadd29c; original global index 13190.
def localCycle00190 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 3 6, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 33 1]

-- Original cycle aa5a28b1d425a1623efcfd2567eb5c124a24ef0f7e7f6fac8ea49f0ecda7e1f1; original global index 13267.
def localCycle00191 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle aa69d9d6ad1ec5c4f6493c04afc71888cd8b6323661580cfac78ff10bce96b2e; original global index 13273.
def localCycle00192 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle abdc179100f17306ea0ce2b0f9a02bcddd34653d14ae6f29dfafce2ae324c652; original global index 13382.
def localCycle00193 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle abedbe0b1feb6703fe65a8d0e7a16d8d658e260fc86fa9a362cd682f1fca9836; original global index 13391.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .triangle 21 2, .triangle 23 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle acc740069bda5187af0264a062e8f5ae4f63ac48af3e097d99e8f52515837053; original global index 13468.
def localCycle00195 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .triangle 33 1, .triangle 34 0, .triangle 28 0, .triangle 16 0]

-- Original cycle ae63145fd0add32c98298948bf742b1c75334316f01ec943bbff40da54d5379c; original global index 13608.
def localCycle00196 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle aed0b83bc875f01e5d2a5691f0a5d1e896f125a15476453e23f3a19366f6af1e; original global index 13645.
def localCycle00197 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 5, .distance 0 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 3 2, .triangle 14 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b03c1b4d343087020b86382034c6831388843f98d7f13394842011e1ab969810; original global index 13758.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle b0607dac2d3aa423d6e42b7182e15ba4268cc34407062a0a9c1f7d128b541f77; original global index 13769.
def localCycle00199 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 1, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b10b86a8d035ae299feaf114f2aa8b62ac42a435932a33540e3c878fed1abf78; original global index 13820.
def localCycle00200 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b1d2caf629a7953d5ff0929f59c99261209546e0a8c04d1f8aac6e615a2fd7f1; original global index 13898.
def localCycle00201 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .gapLower 1 4, .triangle 18 0, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b1d43d2ac4cbe9c84d4b0674718b5f55c62492170d2dac0efe6b79a7eca41d91; original global index 13900.
def localCycle00202 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, 2, -2, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapUpper 4 4, .gapLower 6 5, .gapLower 6 4, .triangle 18 0]

-- Original cycle b4c3377981e44cbc1395a45f7a17e43f78f4d5eb380e5302152c6fb1f16c271d; original global index 14114.
def localCycle00203 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b685ae6741dd516ec785bc91c91432f4c55e312884b2e8bf8803b17f666f2150; original global index 14264.
def localCycle00204 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle b7928d083c2047b3de0065bc8dbe7bd24f621757147f5023cdeff9c79ccf3539; original global index 14324.
def localCycle00205 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 13 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b8f7bac3aabec3988c0534720643f4d2d323aeb1d98397b6fb18662d506b9f6f; original global index 14438.
def localCycle00206 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 1 6, .distance 4 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 23 1, .triangle 34 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle bb3fe50da288440016fc0002d4508e299d0d7b48f8c7f277739c9e18f34f99a9; original global index 14622.
def localCycle00207 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle bb8cda96934fc1d7a14d7f65f213faa1fb644aa0e87dc0ec4d9d72a26bb9a379; original global index 14639.
def localCycle00208 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .gapLower 3 0]

-- Original cycle bbb5e4b44c4c63428314d8cf10f3c27b487134e3eb7c836fdfab800f86c3a06c; original global index 14658.
def localCycle00209 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 19 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle bcd1321cdb6bcb41b01119606379faf0bed471cb1c33914bd46004f5394ba0cd; original global index 14730.
def localCycle00210 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 22 1, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle bd0eda37dc42d793ae0ddaf3895c7f112e8a3e98c75fda177cc3f4405749b1ac; original global index 14750.
def localCycle00211 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 24 1, .triangle 14 0, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle bd31fd991e97b099473b3a91a775a93fd0f224dc26a1543d6c8b5916ce6ded0c; original global index 14759.
def localCycle00212 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 31 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle be47ae609a2b21aa0f6d888ca4302cb0abd176c055175aa3524b17309e02565f; original global index 14841.
def localCycle00213 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 28 0, .triangle 16 0, .triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle befecb0f8441e2f3f5fa3399baf1fbb3cf839f882a589c9ea51df7df8b77e235; original global index 14902.
def localCycle00214 : Cycle where
  length := 4
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .theta 6]
    constant := ![3, -2, 0, -2]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.corridorUpper 5 6, .gapLower 6 5, .triangle 11 2, .gapLower 6 0]

-- Original cycle bfad18874e6a92beaaedaf55b4cac4e947b56ae946e14eea775dd0b76d693829; original global index 14951.
def localCycle00215 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 0, .triangle 34 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle bfd4f6d9f6ceab845b569cb59ee47ee7df80622da0d56f0964024018b89e18ce; original global index 14967.
def localCycle00216 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle bff76bf118106b77eb482d69cdc9c0625a40775a8fac23e47b9cd94cb39ee36c; original global index 14983.
def localCycle00217 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 16 2, .triangle 22 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c196da342e06ddb7cf769424a8d264d138c962e997f05f1917bab9d8bafa601f; original global index 15120.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c1d94181ad985d8c7dc56b920226e2b92bef8febdb01bfcec418df1c45bdac5a; original global index 15136.
def localCycle00219 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 0, .triangle 7 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c303b1b972249aa82d33c32ec5565ea9f5475e55e1841181ed7737c308543fe8; original global index 15221.
def localCycle00220 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 4 5, .distance 3 4, .distance 3 6, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 28 0, .triangle 31 0, .triangle 32 2, .gapLower 3 0, .thetaNext 2]

-- Original cycle c344cc63402dd08b9ce79c85f797170fb1b5f492fbe5b151634ba087de89b046; original global index 15234.
def localCycle00221 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 18 0, .triangle 8 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c48b1f0221213ab24a427a6de12ca21e3d3c2cc91cb7cbc40a942461d8253d38; original global index 15327.
def localCycle00222 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c4e228721a6c3a3247b0eedb138bb795f2562822b68c0233889d8562ed85d42f; original global index 15358.
def localCycle00223 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .gapLower 2 4, .triangle 16 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle c639ef71e66121271b615317ec6dc42b2e997ecc1d31cfd29d4713af75a132f7; original global index 15458.
def localCycle00224 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .triangle 24 1, .triangle 14 0, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c694bb3fbca7b4992f0066b7ff67173b3ca4efbc25c8de10037531885216735a; original global index 15487.
def localCycle00225 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 5 6, .theta 6, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, -2, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .gapUpper 5 0, .gapLower 6 0, .gapLower 6 6, .triangle 29 0, .triangle 6 0, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c781294450e83b072d240a77a9d433680bcf3a881cee33ca1416404627715815; original global index 15570.
def localCycle00226 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle c8c5ca5a725e07467f9a2cf70698b52644704997577491c92c468e8cc6498134; original global index 15682.
def localCycle00227 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 3 6, .distance 0 3, .distance 0 2, .distance 2 4, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 27 0, .triangle 11 0, .triangle 5 1, .triangle 6 0, .triangle 28 2, .corridorLower 2 5]

-- Original cycle ca5e60c41d577c5960523c3aeb0839650a1e4753c48b8ed5381775b97af97f09; original global index 15818.
def localCycle00228 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .triangle 24 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle ca982007835bc91503b6346b8aabffb541f4fd877672632a4b4154efcd4706ff; original global index 15839.
def localCycle00229 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle cb02088b1cdd07332c3a8df11713ccfd604cc5091777cdc966860f6f8071299c; original global index 15862.
def localCycle00230 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle cbfd9b76c2ddab4819ec73ee6014b27ada2d259fc928d71dc90e48002e5188c4; original global index 15941.
def localCycle00231 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 2, .corridorLower 4 6]

-- Original cycle cc3339fb87d690e173ed093a1d45440ba843e7c9211487b6ff4799f79fc4f7a4; original global index 15964.
def localCycle00232 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle cd691b367a373569177be3c7c8eb7014226edd0a19cec76bc6959bef48846484; original global index 16056.
def localCycle00233 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle cff912e2debd824c0f07328bf19c3831cb50d26ed326374489264f2c9b96ac0f; original global index 16235.
def localCycle00234 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle d04414905b848fc5ad8d7d6fdb54352ed0190fe86587b53498457bf8c1024e51; original global index 16255.
def localCycle00235 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle d0dc42bcad3f574d56b4ebc9333f972d1cf40dcc5c23a55e58bf061ebde6fd8c; original global index 16306.
def localCycle00236 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -3, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle d311f04a6e4feb363a87f3ff463d8939a636159fa6c51eaf5f2febd98c2e6c5e; original global index 16464.
def localCycle00237 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 26 2, .triangle 17 0, .triangle 0 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle d3e152a8f57e0b2f2fcd95b6806e950f724a231e7d781db98d230cbf79f6290f; original global index 16538.
def localCycle00238 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle d4d3fb3ca57fee1251977f836944f996f00dd484d528ac82297fb92083addcb8; original global index 16603.
def localCycle00239 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle d54e445b18b32eecb77d8403190b8f775070e0c1830544a7af78c95b7a440eb9; original global index 16646.
def localCycle00240 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 2, .triangle 24 1, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d6401bc0dccbca64ade376d5058a576b8a080886e5a0ff4827b5f811c082cf80; original global index 16725.
def localCycle00241 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 0 2, .triangle 5 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle d65642200682fb5f815bef901bdc445b21b5d94a8c46a5cc2e15d1a5cddc2e3c; original global index 16734.
def localCycle00242 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle d71afc95b76878cecadaf895267ea3d462b5f1e3fdf30f8866d598948bec82cc; original global index 16788.
def localCycle00243 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle d7508d4698c86a1c782d6b795770eb06bc821d4757289cab04bce58f969217db; original global index 16803.
def localCycle00244 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 1 4, .distance 1 6, .distance 0 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![4, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 22 0, .triangle 23 2, .gapLower 6 3, .triangle 13 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle da4fc52a19117036cccc9f98297d24d23d49a57d213676653de146db6766ad11; original global index 17056.
def localCycle00245 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 4 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -2, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 23 0, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle dc662a1f7a65104e6606a67a50c057e488a6bce3bb75e58047dfa3e5b97b9fac; original global index 17224.
def localCycle00246 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, 0, -2, 0, -2, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 24 2, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle dcc668307ba434ab2f090713d94fb045571dc40bcab76b3895e85140572789c1; original global index 17251.
def localCycle00247 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 2]
    constant := ![0, 2, 2, -2, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 2, .gapUpper 3 3, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 18 0]

-- Original cycle deba377f5c0304c063a1d8acca003c5bc05ee8a5bf9c7b48fa2a86f7a33281a1; original global index 17413.
def localCycle00248 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle dec33e55ba53f272fff8e6f68eb23d462d2e490b981f7c7956ed99a6adb48a61; original global index 17417.
def localCycle00249 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 28 1, .triangle 16 0, .triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle dec35da5bc599120d8c2790578f71d7842483d4714a9cd38a72cb02ab1521957; original global index 17418.
def localCycle00250 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 29 1, .triangle 34 1, .triangle 14 0, .triangle 7 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e0e396fc2f7e4ae6328051fc09b2865ee219f1e2028d67cad9335883ec209600; original global index 17583.
def localCycle00251 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 14 0, .triangle 12 1, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e12a73b111222c022c5ec7fa04477c88fa8a71deb6637cfc318dbe8a1779bf59; original global index 17608.
def localCycle00252 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -3, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 13 2, .gapLower 6 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle e35b2772ae1a61a83a3a5b046e0db3e1536d7842f45f9a8c71ba914bc0acf2f0; original global index 17779.
def localCycle00253 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -3, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle e5e08aab2e8912337bf58c3b583aec5a415142ddea6ab736e352e4d3c12fc40d; original global index 17986.
def localCycle00254 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle e8671c95d6c07f4de0d767ddea4b04c2fff6b4135390dcf4d787f822c1aef059; original global index 18168.
def localCycle00255 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle e8b1f903526d00b22782c504ce9455a4e0fc025c23550d7a0315ae3a2513a3db; original global index 18187.
def localCycle00256 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .triangle 23 2, .gapLower 6 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle e8d73106310bba4bb05a378b1f9033dd4a3fb56ffb9b7822ad80a72f4042abb9; original global index 18199.
def localCycle00257 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 8 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle e8e09e62a851a74783ed11550606255ef71a2f43a6cb54d9ae374b6df9a7eac7; original global index 18201.
def localCycle00258 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle ea4d1b09e0e56cdb8f6094e44a5331319ad114e1867bf6573a424a1121543a97; original global index 18297.
def localCycle00259 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 6, .distance 2 6, .distance 1 6, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle eb23cda9ef973e4f97a7bbf3751def6345a51a3dae06a800fcca9e9e5d8c06b8; original global index 18360.
def localCycle00260 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .distance 0 6, .theta 0, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .triangle 24 1, .gapLower 6 1, .corridorLower 0 6, .thetaLower 0]

-- Original cycle ebdf8e86fb63a3dee6c55180a80ba01737b801c5606238ecf71502ab4d9c2052; original global index 18408.
def localCycle00261 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 22 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ec968939bc4af53f02dadae825cd22e0991c59f561eb9672c0b9946034a486d0; original global index 18471.
def localCycle00262 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, -1, 0]
    strict := ![false, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle eda9da67fd491fefd1f35e0602e5c3cb1bd9842649f70fc7f612592e18da9a3d; original global index 18554.
def localCycle00263 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 2 4, .distance 1 2, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 29 1, .triangle 16 0, .triangle 0 2, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ee22b45e5732af14660abe133ddec3116e899aa4aa8c8ef4984f6b95e7fd4641; original global index 18587.
def localCycle00264 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle ee90d1af4f0849e0028d97849b415f5bcb7f4728503388021f55878586fd04c7; original global index 18618.
def localCycle00265 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle efefa3ee495cd849a1a4c26045a3ac41178fa31fcc9ef8a51bab495dfba6a98e; original global index 18723.
def localCycle00266 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle f002850e4790ea8e86f8e1747178d8a9c8523062804652aa588857382d6ecbdc; original global index 18726.
def localCycle00267 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .theta 0, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 21 0, .triangle 1 0, .corridorLower 0 1, .thetaLower 0]

-- Original cycle f032a0d574805f7879f4869ae55bb4d15151c1b4b3a609d7bff1b87f080e9817; original global index 18734.
def localCycle00268 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle f06520b4da1ec57c7e6648c0a580d3775e3576d415c9d5bf736d81d2a539566b; original global index 18745.
def localCycle00269 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, 0, -2, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .triangle 30 1, .gapLower 6 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle f1a8388928e84a50ee022bf2648db0ae6dbe5532cebbc5c633e604cb6c394ef8; original global index 18842.
def localCycle00270 : Cycle where
  length := 5
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .theta 6]
    constant := ![3, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 0]

-- Original cycle f1d9229fef0bc0de34a2d20a76f8cc455135bf5be762619f172f3b88a11f3053; original global index 18858.
def localCycle00271 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 0 4, .distance 0 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 22 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f5e629243e486ccc4fe9a96d46c7eddcdfe10d01aec7cf4f9fc82822b6f11c93; original global index 19187.
def localCycle00272 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 19 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle f7daf736ee43bd5f54ed133e1a337364358b594eb8fce8881824439fd78a551f; original global index 19322.
def localCycle00273 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 1 2, .triangle 15 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 32 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle f819bf1aed0d6bea04a3f93ea1a804db51651aec17088de78ddbe61c52de3af0; original global index 19344.
def localCycle00274 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 4, .distance 1 5, .distance 1 6, .distance 4 6, .distance 0 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, 0, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 2, .triangle 22 2, .triangle 24 2, .gapLower 6 3, .gapLower 6 2, .triangle 14 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle f8ff6805347261315bd8fe541be955420b9eb8443e00a338c88b72f2ea9aaa8a; original global index 19419.
def localCycle00275 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 1 6, .distance 1 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 6 4, .triangle 18 1]

-- Original cycle f9cf27dc9314ee6f3e076c7bd7320c347a2305cc0dcb678db2a766cd24b46e4f; original global index 19481.
def localCycle00276 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .triangle 4 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle f9fc66988b02588fb4aedf16f82209d048080ade318c735cd9dcb1dd647f836b; original global index 19493.
def localCycle00277 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 4 6, .distance 1 6, .distance 1 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 6 3, .triangle 23 1]

-- Original cycle fb706bb6798271e2a15f9ec2e81bc913f1656544be800e39879810c10559657b; original global index 19629.
def localCycle00278 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 4 6, .distance 1 6, .distance 0 6, .distance 5 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 34 2, .gapLower 6 3, .triangle 4 2, .triangle 14 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle fc227e414ff913b3888d6ff871247177f955bca056bc586e23df2898a99ebf5e; original global index 19689.
def localCycle00279 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 0 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -3, 0, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 2, .gapLower 6 1, .triangle 14 1, .triangle 12 1, .triangle 6 1, .triangle 0 1, .corridorLower 0 1, .thetaLower 0]

-- Original cycle fd057e4cc948e799240eb14a79e86949e5857fa2a2610b9652a8d74ab90635a8; original global index 19774.
def localCycle00280 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle fe8b07362ba04103c6e8cfde89fb877d6a7c7f19ce13f191402c4299144ec7b1; original global index 19898.
def localCycle00281 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, -1, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle ff1541e97041d3d2f41358b19cd902eebb0717e30b69c58d6062840811b69d2b; original global index 19943.
def localCycle00282 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 0, .triangle 22 0, .triangle 23 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

def library : Library := fun id => if id < 141 then (if id < 70 then (if id < 35 then (if id < 17 then (if id < 8 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none)))) else (if id < 12 then (if id < 10 then (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none)) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))) else (if id < 14 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none)) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))))) else (if id < 26 then (if id < 21 then (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))))) else (if id < 30 then (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))))))) else (if id < 52 then (if id < 43 then (if id < 39 then (if id < 37 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)))) else (if id < 47 then (if id < 45 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none)) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))) else (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)))))) else (if id < 61 then (if id < 56 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))) else (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))))) else (if id < 65 then (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 67 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))))))) else (if id < 105 then (if id < 87 then (if id < 78 then (if id < 74 then (if id < 72 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none))) else (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none)))) else (if id < 82 then (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))) else (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))))) else (if id < 96 then (if id < 91 then (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 93 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none)) else (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))))) else (if id < 100 then (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none))) else (if id < 102 then (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none)) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))))))) else (if id < 123 then (if id < 114 then (if id < 109 then (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))) else (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))))) else (if id < 118 then (if id < 116 then (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none)) else (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none))) else (if id < 120 then (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))))) else (if id < 132 then (if id < 127 then (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))))) else (if id < 136 then (if id < 134 then (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)) else (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none))) else (if id < 138 then (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))))))))) else (if id < 212 then (if id < 176 then (if id < 158 then (if id < 149 then (if id < 145 then (if id < 143 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id = 142 then some localCycle00142 else none)) else (if id < 144 then (if id = 143 then some localCycle00143 else none) else (if id = 144 then some localCycle00144 else none))) else (if id < 147 then (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none)))) else (if id < 153 then (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))) else (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none)))))) else (if id < 167 then (if id < 162 then (if id < 160 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id = 166 then some localCycle00166 else none))))) else (if id < 171 then (if id < 169 then (if id < 168 then (if id = 167 then some localCycle00167 else none) else (if id = 168 then some localCycle00168 else none)) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none))) else (if id < 173 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none)) else (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))))))) else (if id < 194 then (if id < 185 then (if id < 180 then (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none))))) else (if id < 189 then (if id < 187 then (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))) else (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)))))) else (if id < 203 then (if id < 198 then (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))) else (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))))) else (if id < 207 then (if id < 205 then (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)) else (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id = 206 then some localCycle00206 else none))) else (if id < 209 then (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none)) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)))))))) else (if id < 247 then (if id < 229 then (if id < 220 then (if id < 216 then (if id < 214 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none))) else (if id < 218 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none)))) else (if id < 224 then (if id < 222 then (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id = 221 then some localCycle00221 else none)) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none))) else (if id < 226 then (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id = 225 then some localCycle00225 else none)) else (if id < 227 then (if id = 226 then some localCycle00226 else none) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)))))) else (if id < 238 then (if id < 233 then (if id < 231 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none)) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none))) else (if id < 235 then (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none))))) else (if id < 242 then (if id < 240 then (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id = 239 then some localCycle00239 else none)) else (if id < 241 then (if id = 240 then some localCycle00240 else none) else (if id = 241 then some localCycle00241 else none))) else (if id < 244 then (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none)) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none))))))) else (if id < 265 then (if id < 256 then (if id < 251 then (if id < 249 then (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id = 248 then some localCycle00248 else none)) else (if id < 250 then (if id = 249 then some localCycle00249 else none) else (if id = 250 then some localCycle00250 else none))) else (if id < 253 then (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)) else (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none))))) else (if id < 260 then (if id < 258 then (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id = 257 then some localCycle00257 else none)) else (if id < 259 then (if id = 258 then some localCycle00258 else none) else (if id = 259 then some localCycle00259 else none))) else (if id < 262 then (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none)) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none)))))) else (if id < 274 then (if id < 269 then (if id < 267 then (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id = 266 then some localCycle00266 else none)) else (if id < 268 then (if id = 267 then some localCycle00267 else none) else (if id = 268 then some localCycle00268 else none))) else (if id < 271 then (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none)) else (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none))))) else (if id < 278 then (if id < 276 then (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id = 275 then some localCycle00275 else none)) else (if id < 277 then (if id = 276 then some localCycle00276 else none) else (if id = 277 then some localCycle00277 else none))) else (if id < 280 then (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none)) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 0, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 164 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4352)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 0, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 2, 6, 0, 1], ![3, 4, 2, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 204 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4353)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 3, 2], ![5, 6, 4, 0, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 128 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4354)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 0, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 128 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4355)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 0, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 43 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4356)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 0, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 5, 6, 2, 0, 1], ![3, 4, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 31 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4357)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 0, 3, 1], ![4, 5, 6, 0, 2, 1], ![3, 6, 5, 2, 0, 1], ![3, 6, 4, 2, 0, 1], ![3, 5, 4, 2, 0, 1]], proof := .tail 199 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4358)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 0, 3, 1], ![4, 6, 5, 0, 2, 1], ![3, 6, 5, 2, 0, 1], ![6, 3, 4, 2, 0, 1], ![5, 3, 4, 2, 0, 1]], proof := .tail 181 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4359)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 0, 3, 1], ![6, 4, 5, 0, 2, 1], ![6, 3, 5, 2, 0, 1], ![6, 3, 4, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 220 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4360)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 3, 2, 6], ![5, 4, 0, 3, 1, 6], ![5, 4, 0, 2, 1, 6], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 212 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4361)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 3, 6, 2], ![5, 4, 0, 3, 6, 1], ![5, 4, 0, 2, 1, 6], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 90 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4362)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 6, 3, 2], ![5, 4, 0, 3, 6, 1], ![5, 4, 0, 2, 6, 1], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 134 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4363)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 6, 4, 3, 2], ![5, 4, 0, 3, 6, 1], ![5, 4, 0, 2, 6, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![0, 2, 3, 4, 1, 5]], proof := .tail 54 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4364)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 6, 5, 4, 3, 2], ![5, 4, 0, 3, 6, 1], ![5, 4, 0, 2, 6, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![0, 2, 3, 4, 5, 1]], proof := .tail 46 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4365)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 4, 6, 3, 2], ![5, 4, 0, 6, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![0, 3, 2, 1, 4, 5]], proof := .tail 227 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4366)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 5, 6, 4, 3, 2], ![5, 4, 0, 6, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![0, 3, 2, 4, 1, 5]], proof := .tail 227 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4367)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![1, 5, 4, 2, 3, 6], ![0, 6, 5, 4, 3, 2], ![5, 4, 0, 6, 3, 1], ![5, 4, 0, 6, 2, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![0, 3, 2, 4, 5, 1]], proof := .tail 227 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4368)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 4, 6, 3, 2], ![5, 4, 0, 6, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![3, 0, 2, 1, 4, 5]], proof := .tail 116 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4369)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 5, 6, 4, 3, 2], ![5, 4, 0, 6, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![3, 0, 2, 4, 1, 5]], proof := .tail 102 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4370)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![1, 5, 4, 2, 6, 3], ![0, 6, 5, 4, 3, 2], ![5, 4, 0, 6, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![3, 0, 2, 4, 5, 1]], proof := .tail 209 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4371)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 5, 4, 6, 3, 2], ![5, 4, 6, 0, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 6], ![3, 2, 0, 1, 4, 5]], proof := .tail 120 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4372)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 5, 6, 4, 3, 2], ![5, 4, 6, 0, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 1, 6], ![3, 2, 0, 4, 1, 5]], proof := .tail 167 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4373)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![1, 5, 4, 6, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 0, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 6, 1], ![3, 2, 0, 4, 5, 1]], proof := .tail 55 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4374)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 3, 2], ![5, 4, 6, 0, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 1, 6], ![3, 2, 4, 0, 1, 5]], proof := .tail 86 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4375)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 0, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 0, 6, 1], ![3, 2, 4, 0, 5, 1]], proof := .tail 86 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4376)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 4, 6, 0, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 2, 6, 0, 1], ![4, 3, 2, 6, 0, 1], ![3, 2, 4, 5, 0, 1]], proof := .tail 43 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4377)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 3, 2], ![5, 6, 4, 0, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 0, 1, 6], ![3, 4, 2, 0, 1, 5]], proof := .tail 156 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4378)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 0, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 0, 6, 1], ![3, 4, 2, 0, 5, 1]], proof := .tail 156 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4379)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 0, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 2, 6, 0, 1], ![3, 4, 2, 5, 0, 1]], proof := .tail 43 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4380)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 0, 3, 1], ![5, 4, 6, 0, 2, 1], ![5, 3, 6, 2, 0, 1], ![4, 3, 6, 2, 0, 1], ![3, 4, 5, 2, 0, 1]], proof := .tail 63 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4381)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 5, 6, 4, 3, 2], ![5, 6, 4, 0, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 0, 1, 6], ![4, 3, 2, 0, 1, 5]], proof := .tail 273 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4382)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![1, 5, 6, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 0, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 0, 6, 1], ![4, 3, 2, 0, 5, 1]], proof := .tail 273 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4383)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![5, 6, 4, 0, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 2, 6, 0, 1], ![4, 3, 2, 5, 0, 1]], proof := .tail 43 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4384)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 0, 3, 1], ![5, 6, 4, 0, 2, 1], ![5, 6, 3, 2, 0, 1], ![4, 3, 6, 2, 0, 1], ![4, 3, 5, 2, 0, 1]], proof := .tail 63 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4385)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 0, 3, 1], ![6, 5, 4, 0, 2, 1], ![5, 6, 3, 2, 0, 1], ![4, 6, 3, 2, 0, 1], ![4, 5, 3, 2, 0, 1]], proof := .tail 196 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4386)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![1, 6, 5, 4, 2, 3], ![0, 6, 5, 4, 3, 2], ![6, 5, 4, 0, 3, 1], ![6, 5, 4, 0, 2, 1], ![6, 5, 3, 2, 0, 1], ![6, 4, 3, 2, 0, 1], ![5, 4, 3, 2, 0, 1]], proof := .tail 59 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4387)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 0, 1, 4, 5, 6], ![0, 1, 2, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 34 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4388)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 0, 1, 4, 5, 6], ![0, 1, 2, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 177 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4389)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 0, 1, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 249 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4390)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 0, 1, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 223 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4391)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 6, 5], ![2, 0, 1, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .low6 (![276, 279, 10, 230, 19, 23, 189, 233, 149, 239, 186, 105, 92, 255, 246, 159, 64, 123, 14, 41, 269, 255, 79, 172, 94, 2, 242, 187]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4392)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 6, 5], ![2, 0, 1, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 148 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4393)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 2, 3]], proof := .tail 28 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4394)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 4, 6, 5], ![2, 0, 1, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low6 (![150, 185, 33, 113, 144, 23, 130, 114, 8, 235, 71, 216, 92, 53, 81, 228, 260, 133, 112, 198, 232, 20, 147, 107, 211, 202, 224, 267]) }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4395)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 4, 6, 5], ![2, 0, 1, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 4, 3]], proof := .tail 148 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4396)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 4, 2, 3]], proof := .tail 251 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4397)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 6, 4, 5], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 1, 2, 3]], proof := .tail 56 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4398)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 1, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 1, 3]], proof := .tail 266 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4399)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 4, 5], ![0, 6, 1, 2, 3, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 4, 2, 3, 1]], proof := .tail 174 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4400)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 4, 6, 5], ![2, 0, 1, 4, 6, 5], ![0, 1, 2, 3, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low6 (![96, 226, 1, 117, 144, 23, 130, 197, 25, 161, 110, 66, 225, 9, 84, 61, 264, 92, 11, 101, 108, 92, 147, 107, 142, 202, 263, 267]) }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4401)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 4, 6, 5], ![2, 0, 1, 6, 4, 5], ![0, 1, 2, 6, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 4, 3]], proof := .tail 148 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4402)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 4, 5], ![0, 1, 6, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 4, 2, 3]], proof := .tail 68 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4403)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 2, 6, 4, 5], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 1, 2, 3]], proof := .tail 21 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4404)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 6, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 1, 6, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 1, 3]], proof := .tail 266 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4405)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 3, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 4, 5], ![0, 6, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 4, 2, 3, 1]], proof := .tail 205 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4406)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 2, 6, 4, 5], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 1, 2, 3]], proof := .low6 (![141, 135, 168, 103, 275, 4, 170, 47, 165, 85, 85, 80, 85, 131, 244, 139, 80, 15, 111, 6, 80, 38, 52, 80, 62, 65, 176, 80]) }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4407)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 6, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 1, 6, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 2, 1, 3]], proof := .tail 51 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4408)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 3, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 0, 2, 3, 1]], proof := .tail 193 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4409)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 3, 6, 2, 4, 5], ![3, 6, 0, 1, 4, 5], ![2, 0, 1, 6, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 0, 1, 3]], proof := .tail 44 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4410)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 3, 2, 4, 5], ![3, 6, 0, 1, 4, 5], ![2, 0, 6, 1, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 0, 3, 1]], proof := .tail 26 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4411)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 2, 4, 5], ![3, 6, 0, 1, 4, 5], ![2, 6, 0, 1, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 2, 3, 0, 1]], proof := .tail 218 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4412)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 2, 4, 5], ![6, 3, 0, 1, 4, 5], ![6, 2, 0, 1, 4, 5], ![6, 0, 1, 2, 3, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 0, 1]], proof := .tail 129 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4413)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 0, 1, 5, 4, 6], ![0, 1, 2, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 192 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4414)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 0, 1, 5, 6, 4], ![0, 1, 2, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 213 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4415)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 0, 1, 6, 5, 4], ![0, 1, 2, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 195 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4416)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 5, 6], ![2, 0, 1, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 153 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4417)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 4, 6, 5], ![2, 0, 1, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 280 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4418)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 125 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4419)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 4, 6, 5], ![2, 0, 1, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 2, 4, 3]], proof := .tail 88 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4420)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 1, 4, 2, 3]], proof := .tail 240 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4421)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 6, 4, 5], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 1, 2, 3]], proof := .tail 146 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4422)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 1, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 180 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4423)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 5, 4], ![0, 6, 1, 2, 5, 3], ![0, 6, 1, 2, 4, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 180 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4424)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 4, 6, 5], ![2, 0, 1, 6, 5, 4], ![0, 1, 2, 6, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 2, 4, 3]], proof := .tail 88 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4425)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 5, 4], ![0, 1, 6, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 1, 4, 2, 3]], proof := .tail 265 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4426)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 2, 6, 4, 5], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 1, 2, 3]], proof := .tail 39 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4427)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 6, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 1, 6, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 95 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4428)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 3, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 5, 4], ![0, 6, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 95 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4429)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 2, 6, 4, 5], ![3, 0, 1, 6, 4, 5], ![2, 0, 1, 6, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 0, 1, 2, 3]], proof := .tail 182 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4430)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 6, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 1, 6, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 73 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4431)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 3, 2, 4, 5], ![3, 0, 6, 1, 4, 5], ![2, 0, 6, 1, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 73 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4432)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 3, 6, 2, 4, 5], ![3, 6, 0, 1, 4, 5], ![2, 0, 1, 6, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 0 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4433)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 3, 2, 4, 5], ![3, 6, 0, 1, 4, 5], ![2, 0, 6, 1, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 257 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4434)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 2, 4, 5], ![3, 6, 0, 1, 4, 5], ![2, 6, 0, 1, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 257 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4435)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 2, 4, 5], ![6, 3, 0, 1, 4, 5], ![6, 2, 0, 1, 5, 4], ![6, 0, 1, 2, 5, 3], ![6, 0, 1, 2, 4, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 241 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4436)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 4, 6], ![0, 1, 5, 2, 3, 6], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 97 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4437)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 6, 4], ![0, 1, 5, 2, 6, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 208 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4438)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 6, 5, 4], ![0, 1, 5, 2, 6, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 261 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4439)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .low6 (![145, 188, 236, 154, 253, 190, 219, 243, 268, 17, 191, 214, 40, 268, 138, 222, 155, 29, 258, 42, 12, 268, 24, 32, 152, 169, 281, 262]) }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4440)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 6, 5, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 271 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4441)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 1, 5, 6, 2, 3], ![0, 1, 4, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 254 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4442)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 5, 6], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 1, 6, 4, 2, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 157 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4443)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 1, 4, 2, 3]], proof := .tail 119 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4444)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 6, 4, 5], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 1, 2, 3]], proof := .tail 16 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4445)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 2, 4, 5], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 93 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4446)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 2, 4, 5], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![0, 6, 1, 5, 2, 3], ![0, 6, 1, 4, 2, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 93 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4447)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 2, 4, 6, 5], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 1, 6, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 1, 4, 2, 3]], proof := .low6 (![96, 252, 58, 277, 171, 4, 170, 166, 256, 278, 151, 80, 3, 234, 143, 151, 80, 178, 229, 151, 80, 158, 160, 104, 60, 115, 151, 80]) }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4448)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 2, 6, 4, 5], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 1, 2, 3]], proof := .tail 18 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4449)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 6, 2, 4, 5], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 282 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4450)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 3, 2, 4, 5], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![0, 6, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 100 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4451)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 2, 6, 4, 5], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 0, 1, 2, 3]], proof := .tail 179 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4452)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 6, 2, 4, 5], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 201 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4453)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 3, 2, 4, 5], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 57 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4454)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 3, 6, 2, 4, 5], ![3, 6, 0, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 2, 0, 1, 3]], proof := .tail 106 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4455)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![1, 3, 6, 2, 4, 5], ![0, 6, 3, 2, 4, 5], ![3, 6, 0, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 2, 0, 3, 1]], proof := .tail 36 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4456)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 2, 4, 5], ![3, 6, 0, 1, 5, 4], ![2, 6, 0, 1, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 2, 3, 0, 1]], proof := .tail 72 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4457)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![1, 6, 3, 2, 4, 5], ![0, 6, 3, 2, 4, 5], ![6, 3, 0, 1, 5, 4], ![6, 2, 0, 1, 5, 4], ![6, 0, 1, 5, 2, 3], ![6, 0, 1, 4, 2, 3], ![5, 4, 3, 2, 0, 1]], proof := .tail 175 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4458)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 4, 6], ![0, 5, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 77 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4459)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 5, 6, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 1, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 217 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4460)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 4, 6], ![2, 0, 1, 6, 5, 4], ![0, 5, 1, 2, 6, 3], ![0, 4, 1, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 173 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4461)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 203 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4462)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 99 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4463)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 5, 4, 6], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 1, 6, 2, 3], ![0, 4, 1, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 248 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4464)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 5, 6, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 2, 3, 6], ![0, 4, 1, 2, 3, 5]], proof := .low6 (![45, 37, 30, 184, 136, 190, 124, 238, 22, 126, 270, 214, 237, 13, 35, 78, 194, 245, 207, 231, 27, 98, 259, 49, 206, 247, 75, 70]) }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4465)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 5, 6, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 2, 6, 3], ![0, 4, 1, 2, 5, 3]], proof := .tail 210 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4466)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 5, 6, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 1, 6, 2, 3], ![0, 4, 1, 5, 2, 3]], proof := .tail 89 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4467)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 1, 2, 3]], proof := .tail 163 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4468)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 1, 2, 3]], proof := .tail 82 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4469)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 2, 1, 3]], proof := .tail 137 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4470)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 2, 1, 3]], proof := .tail 48 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4471)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![0, 5, 6, 1, 2, 3], ![0, 4, 6, 1, 2, 3], ![0, 4, 5, 2, 3, 1]], proof := .tail 272 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4472)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![1, 3, 2, 4, 5, 6], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![0, 6, 4, 1, 2, 3], ![0, 5, 4, 2, 3, 1]], proof := .tail 250 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4473)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 1, 2, 3]], proof := .low6 (![96, 162, 87, 76, 275, 4, 170, 127, 140, 118, 69, 80, 50, 215, 91, 122, 80, 183, 274, 83, 80, 132, 74, 80, 121, 65, 109, 80]) }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4474)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 2, 1, 3]], proof := .tail 5 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4475)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![1, 3, 2, 4, 6, 5], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![0, 6, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 0, 4, 2, 3, 1]], proof := .tail 200 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4476)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 2, 6, 5, 4], ![3, 0, 1, 6, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 0, 1, 2, 3]], proof := .tail 67 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4477)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 3, 6, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 1, 6, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 0, 2, 1, 3]], proof := .tail 221 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4478)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![1, 3, 2, 6, 4, 5], ![0, 6, 3, 2, 5, 4], ![3, 0, 6, 1, 5, 4], ![2, 0, 6, 1, 5, 4], ![6, 0, 5, 1, 2, 3], ![6, 0, 4, 1, 2, 3], ![5, 4, 0, 2, 3, 1]], proof := .tail 7 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 4479)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (4352 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 4352 ≤ id.val) (hhigh : id.val < 4480) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 4352)) = true := by
  let j : Fin 128 := ⟨id.val - 4352, by omega⟩
  have hsum : 4352 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (4352 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard034
