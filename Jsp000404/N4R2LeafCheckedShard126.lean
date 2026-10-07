import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard126
open N4R2RowDataReplay

-- Original cycle 04b1f8eead53c7afdae681c0090794f28cac5280eed5b7a6f87e80ab71367c74; original global index 372.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 05df886d187965af2ee8d4098236fe4f00e2db5640a2d73b03adf81ff259f56c; original global index 487.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 0a5b8cb96d4628421003b67ff6cc564dd3f44b06f0f07ae0c3951585471a3fc2; original global index 826.
def localCycle00002 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .triangle 15 0, .gapLower 2 0]

-- Original cycle 0a85b54569c376aa022bb27f90e6888943df9668b3dd6ff3c25659086e3fa63a; original global index 836.
def localCycle00003 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 0c8d79e256bb3c8c8f57b16a0077e4d7824454e2286255a30fd44e4b6f1131a0; original global index 994.
def localCycle00004 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 0ce12da48802fef35770fbb1c4b4738314df0387ee53748895d95d0e61d216b2; original global index 1015.
def localCycle00005 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 19 0, .gapLower 4 0]

-- Original cycle 16d976d67b4e8f41b62d4459cc7fde53b347fa88511552e2e6304adb7b8a51a6; original global index 1798.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 6 0, .triangle 16 2, .gapLower 4 0]

-- Original cycle 16fdf51535717aa59b8035a9f1ec5cf0cd16997090e44773fb769e1c2197a303; original global index 1808.
def localCycle00007 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Original cycle 196c6f0e5965f0c7b83f3524a222d650f4a5b15af3f2c0b0b28220b3ba278fe0; original global index 1985.
def localCycle00008 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 28 1, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 1ead473998cd5cc619b12a6c4841891d33e1619fe55db9316e7e991e89b56894; original global index 2352.
def localCycle00009 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 22a4b8cc0175c388bfa80cd19ece6332bda81ee1d007d1ce5984cc5f70134983; original global index 2654.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Original cycle 257607c463fdff5088f3c1a8acb771ba2027b57edc9d35593a7d897ce016a553; original global index 2883.
def localCycle00011 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 2a4d2617dc17c9e1140a979c7c1f4d5e20552d5acaa30290807a985abe9e89c7; original global index 3224.
def localCycle00012 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 2c955847a4575e3e75de29d92ba022b22b99da088036c3a18695067d85069a9d; original global index 3408.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 26 0, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 2e1f5d40d93f5b44eb6136182590bea2cbd853fd7f3438ddab7a3a432bbfe7f9; original global index 3524.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 309a6de782126692b2f741e13f6e9730b1bc2963610d53fe32614e58ab9d63a5; original global index 3708.
def localCycle00015 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 3298bd8fea00f09434326e5307eababd7268fa4180a82a6124c09ba1246e5012; original global index 3870.
def localCycle00016 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, false, true, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Original cycle 338cba65925ce50be076c0c6b7c452df0205e906c81c9f7f706aee9e09291813; original global index 3943.
def localCycle00017 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .gapLower 4 0]

-- Original cycle 395301d05cbba8f22aeb02c7a53a2cbb1ff6a66cb57d199a64967dfcb0ac8e24; original global index 4412.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 3ac734f247e176694af3cb145f533083fd4ee7dca0b4763198ac98c70b615b7f; original global index 4540.
def localCycle00019 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 3ca6d263faf26bcef170d0e35edc664397ce35355d070a1d10e437c15b51acf1; original global index 4704.
def localCycle00020 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 3f40020e9fc33a6b847d6e0da34276262644a17e452796bfacf46e7272ee9034; original global index 4885.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Original cycle 4535360a4359f14df07f969c7dfe1c30b5f89d46862c4890e293bfc582bb56b2; original global index 5354.
def localCycle00022 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 471575f1f81187a649572d6cc2381991de178b421838fd910f90d85eb63cf9a2; original global index 5511.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 477461a7c9a4a051738fb2230088fcfe3fac9aa2c8a948e208f76fde9f7c8eb9; original global index 5533.
def localCycle00024 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .triangle 15 0, .gapLower 2 0]

-- Original cycle 478a6531bf65cac9432b0691dbd7d631e18cda430da5afc913db0f6dcb28071c; original global index 5536.
def localCycle00025 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 484c8e07d031272c3a5070ca3c50bb9426353960bd69e84e1053733330baff9b; original global index 5596.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 19 0, .gapLower 4 0]

-- Original cycle 48f4a9ae84f5e16f08aa2d3f31d90c263de91fa2938f55c042a5572dc47599ec; original global index 5648.
def localCycle00027 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 4a4310d0c7c4f53bff56179b9b9c3fa8abae20568abcc65fa3d04685b62bea76; original global index 5761.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 4b2dad272e0e120fec124d08ed99a3199155d7759630531e43b14f8924b8d17a; original global index 5829.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 50c455b1cd4f30a2f070b368a8b89b1caaabca04f27223fd85f769b65b9d417a; original global index 6271.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 54f37cb42ca3749507f4d55badf7b4436c294145139df36b786cc802a58a2472; original global index 6576.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 54f79c9f15b0af348de84ba882310a3bf99bc0e727a2d5d597c872b010532633; original global index 6578.
def localCycle00032 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 5600d174142341506a1632e71403555a282fbb8afd80b35764b591aa5d258f53; original global index 6672.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .gapLower 2 0]

-- Original cycle 56376b71715ab48a62b75949f7c43ab8f811c8234d6493f0deb96de03a1c532f; original global index 6685.
def localCycle00034 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 5818a1d3428231bebdad184ec1cb434c3660609a1bccf54b5e3afc2f4b1a6b13; original global index 6835.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 5c859f2f9e89db158e3df73bb8e861ffa1cf68ca9e12ff315dd15924d52c7593; original global index 7202.
def localCycle00036 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 60fd546398bc802774490b39121644d4b4224b850a8cd3744c57422bd74eb841; original global index 7557.
def localCycle00037 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6107bce52fdf3a2b1700f2b60ab0bd2c78243b692d71086d453ff876bab3f677; original global index 7564.
def localCycle00038 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 2, .triangle 3 0, .triangle 1 2, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 63d78a1d85e0e63a43ca361f333b6c3a7c3f8e162aad30d88d926356519f2b25; original global index 7780.
def localCycle00039 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 65c1cd25ff7c14511f348afb1fc036bbb08c06cbbc364c88dccce95e16f2e3cc; original global index 7917.
def localCycle00040 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 683d90b7a0d04d10d8ce9e36906518635bd43d49e3f4eacc0a20cd3797cfb9f4; original global index 8109.
def localCycle00041 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 69b2346cbf3c2e117cbde5a3561b1c6f0ec4c8fed9787d9056629776dd4ba969; original global index 8229.
def localCycle00042 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 34 1, .gapLower 5 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6a4d2544cb97c461ba2de803683e3f33d73bc5fc02dadc5621ebccca9772ed1d; original global index 8278.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 6b45d1f9af620c776ad784575228abc237ea13c785a0b12e1f6518c729b04a5c; original global index 8350.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 6eeafc7f5453445d653e630d3d592198a54cb673427418161d800daa1952d409; original global index 8605.
def localCycle00045 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 12 0, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6f7aed7e703679e82e52f28ac4f561e6667c341daa8fe2242f1e2469cee711ce; original global index 8645.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 0, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 710130f97e45bc388520f3eda55f513f05e24106282c45c3c63b6abe7b63d91b; original global index 8765.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 74d8cd6abd3800ca9d4f0da30246f32d322beb028c107f8ca57fbac6ab7bea39; original global index 9053.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .gapLower 2 0]

-- Original cycle 78121494b37125d31d50f483dc6e14a5a860e19b48f709b3440c1656c2ce6356; original global index 9282.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 799f54416f3b7155de36ad6d4a23a6c59bffa4348a05b7c062e1f4cbfbf60c80; original global index 9407.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 7bdc8c434e45e3f0b8d057b6138919d634f3c7a7a4576f2d412847d8f7cf63ba; original global index 9577.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 2, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 7bed0ef056370061b2a4641b8fa0399f9a5c52f39ab25f38e475407cb3e39129; original global index 9583.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 28 0, .triangle 22 2, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Original cycle 7cc17cd643317da3e98dbc894d278c8d7b652360c4e45efb7d07a55762b5aa68; original global index 9661.
def localCycle00053 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7ea1a2ccf9c0ed1b32ca34922198c5594aed64012146b314d5f880981b051fe1; original global index 9830.
def localCycle00054 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7fd49be88f163c3b52bb66adf1759f65efb97a7b19ba60eba9ee25d6641b45d5; original global index 9916.
def localCycle00055 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 3 0, .triangle 1 2, .triangle 5 1, .triangle 6 0, .triangle 25 1, .triangle 19 0, .gapLower 3 0]

-- Original cycle 811e98c0b73e88818b3846b52f054ab06ea98f579dfba40069f81bae1d8c7b85; original global index 10021.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle 836cc7511976ca48b19a37285c953c12292c9fe88aba3640857aadf49ecea175; original global index 10196.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 19 0, .gapLower 4 0]

-- Original cycle 8468e49bed68923eb3b543dcfdaf98a9b380fbc8a11cf9f7bf60342a08c2088c; original global index 10283.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 847377b937cabbadc49206616f337f6070925f31f6fa5554d291aa42ebfce543; original global index 10285.
def localCycle00059 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 5 1, .triangle 6 0, .triangle 25 1, .triangle 19 0, .gapLower 3 0]

-- Original cycle 861db0214ca0e29345d1ddeb8350efaa3712aff326e34819c92acc51b3e2fd50; original global index 10402.
def localCycle00060 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 870c31168e46328649f41fda385c58cbe64df3fbe04e3c00ca112c59e5fc1f27; original global index 10476.
def localCycle00061 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .gapLower 5 2, .triangle 3 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 8f51b8aabc70148827750c18be7a02054905414c9b970b96a8735944c84aaf85; original global index 11091.
def localCycle00062 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 90319f9f07745d32367389c15ef4f6d7b7f3856fcd77948bef0c0b903f68bccd; original global index 11162.
def localCycle00063 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 2, .triangle 17 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 90cb4ab6eb2fcc2e39183f2bcb6b65f21280586699c52e2b14981da10bb36060; original global index 11215.
def localCycle00064 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 94d98a116d82ddad8e72d596494717d9d09735fcedc3796214c2478607196950; original global index 11557.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 950a89c10e5b7baadda77e1ab54da2dbdd2422d32be44ef6b070880cd7e8568f; original global index 11573.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4]

-- Original cycle 9d20f692b91d5f8dc0b2a93910823a805d51d83d6867ee3c1803a3e7e7fdd554; original global index 12221.
def localCycle00067 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a236a14d65355e7004dc0736b9ee05ec49e75d0c657a306eb8d3ba2bb23857be; original global index 12621.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 6, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, -1, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 6, .thetaLower 1]

-- Original cycle a39ced24af48f122e25b5c2935805e513638436dac774e4d4b03adf06ca38235; original global index 12717.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Original cycle a53c3b213cc10c63250109c10762e3ecdd8876c07d57a711e5acc7cbf0c7bc1f; original global index 12837.
def localCycle00070 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 34 1, .gapLower 5 2, .triangle 3 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle ac756a2f11ce0e1c4c737540843cb4b1ea4abccb0d1ccda7928bce382b3c1a6a; original global index 13443.
def localCycle00071 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 1 2, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle acb277f92f4d589c34985fbde4cca504578e4f7a0c811a3e3a3cdb17d84e1056; original global index 13463.
def localCycle00072 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Original cycle b174358a4f4926b2b40e8d73fda0644555bebc9e4d40dbb9d0ed8269c15e4a98; original global index 13867.
def localCycle00073 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b40d98a167dac3dcba3708aede65e69798aeb0a04d4fa103d0fe487778369fb1; original global index 14059.
def localCycle00074 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 2, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b95f7ff2f5429086f798a28f672b9439e089b644a1bbeace2dd4c3a983e1a2c7; original global index 14465.
def localCycle00075 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 2, .triangle 5 1, .triangle 6 0, .triangle 25 1, .triangle 19 0, .gapLower 3 0]

-- Original cycle bbd6a559f9b38defba4574341c1672be70e893461cf43d1fb471479e57558059; original global index 14671.
def localCycle00076 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, true, true, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 28 0, .triangle 22 2, .triangle 3 0, .triangle 2 2, .triangle 6 1, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle bccf7df4d87097914528baed403532761a0760461e3cb790920fa086ed7ae454; original global index 14729.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle bf22da0708e0cc1a83a42d73e9e861636f767672bf75969de4c5988cee1fde7a; original global index 14914.
def localCycle00078 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c03735bcbc18bf4f35c456613462f70807acd41edb9af6a9c36947300f810c1c; original global index 15008.
def localCycle00079 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 2, .triangle 33 0, .triangle 34 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c446adbff1e3cacedfd7d71b67ea99ac1029553376ab673cde475fa37d9f10a4; original global index 15312.
def localCycle00080 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle c48cee8bab8a496e759328926d0c3342d40b5c579e949b0e38c8298e5a2a8245; original global index 15328.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c529f20e977f7ff36fe88d04c733cec93d285e13fa1d83b595d4292bfed516fb; original global index 15382.
def localCycle00082 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 2, .triangle 20 2, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c5f5068962b9199c5baef98c6a306b94e7265c020601fb04e79b318081019770; original global index 15438.
def localCycle00083 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c5fc1b3c11dd30c15305a083eedbcb5015b2b5eab5918896843a47f70191d5dd; original global index 15441.
def localCycle00084 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle c921fbfaf667809b43a5d0afc5afbafcc012665a30b10b9a9c499671605720a9; original global index 15713.
def localCycle00085 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 30 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .gapLower 2 0]

-- Original cycle cc27dfa73486a2694675de392f3a9d8f4ef8b05b15e4e2ee5efaf296946a4af3; original global index 15958.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle cebf49871686dea625964a790cc944e41e4f22c229d2cee737a0ae2a5b2dac5b; original global index 16138.
def localCycle00087 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle cfb21f3892712a06057de86be50b9ca2dce6a0ec30ef59d0cb9e9082d980268f; original global index 16209.
def localCycle00088 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle d198676ffcdf7d33f45091140c98b645f422a9c97cc9973721e86a760d231841; original global index 16358.
def localCycle00089 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d30341556553973ec510ed5cb42e9179db3c47c49d9d03037031a0f11e610953; original global index 16460.
def localCycle00090 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![4, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Original cycle d365332c0597af2daa47a6ebc682aa07b08c03f0c105f48054e1177edc01d3c6; original global index 16489.
def localCycle00091 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d3d18f096fc1de888fe32036bdbf0f2c4871f4389990fd9d05a165a7482e39ad; original global index 16530.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 5 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d6724f46af5dd192d3e01c52d4e2b72ba194ca84e712fb46a6519bdabe9b8d78; original global index 16741.
def localCycle00093 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 31 0, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d7c37b6931e5a7ba247447f44f0337b0e593367348a442aa20fed6cb7e0ae651; original global index 16835.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 2 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 0, .triangle 15 0, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle dd64fcb803785047a5c901063a46441793431d471be2561bdc092e7056df0fa5; original global index 17307.
def localCycle00095 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle de7cc38d3a1b1f82fe93249c1ba47a17e3775ed14155306fe78f280bb69ea30a; original global index 17394.
def localCycle00096 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 2, .distance 0 3, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 0 2, .triangle 5 2, .triangle 9 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle dfd10a1bc300c665a358288bc3dd55c3c92afe7950ade5a84fcbcdc880290cb4; original global index 17487.
def localCycle00097 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 10 0, .triangle 9 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle e062f7823d6591b5ac5315bc4dfc1c83a19a7de829ff156b19f3cb4bfb803ef6; original global index 17540.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 26 0, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle e35c7b492411a2251f6787aef403fc44a2c73428ee54cbfa3942645ae871feb4; original global index 17780.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 24 0, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e62f8c76d8e5a90244b72b9038c81f5863df46d0f1fbb7b0f725776ed7185ac0; original global index 18013.
def localCycle00100 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle e9759e8885254a1dfe45ec424a831baa89c5dec3fea32e59b776170b35c5205d; original global index 18244.
def localCycle00101 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 3 0, .triangle 1 2, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Original cycle eb9e7f50095b9a25d557bde4098450798d40e4342021543dc548e8a1e7cc3545; original global index 18384.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 32 0, .triangle 34 1, .gapLower 5 3, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle f07936ca7022575811c45938076c1787d5fd3deac38298e6280178ff95690d75; original global index 18751.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 0 1, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 3 0, .triangle 2 0, .gapLower 4 0]

-- Original cycle f0f9b1c8ec6effdf5381ead508931357bb520352e6daf0eb2b986ef7a664041f; original global index 18795.
def localCycle00104 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 0 3, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 1 2, .triangle 5 1, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle f2d69ee36fc66e0deaa6e16ea5af2786d25575353cd30819c254315866447d14; original global index 18928.
def localCycle00105 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 1 2, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 2, .triangle 3 0, .triangle 1 0, .triangle 15 1, .triangle 16 0, .triangle 25 1, .corridorLower 3 4]

-- Original cycle f5a35eb9118712cf7a992e388a2b3a023ce5980bc726cc059b1dc0f8125076b3; original global index 19153.
def localCycle00106 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0, .triangle 25 2, .triangle 6 0, .triangle 5 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle f640745c447c527da41914f3c7780f183b173127e3795d4060558dd4f166d521; original global index 19209.
def localCycle00107 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 5, .distance 0 1, .distance 1 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .gapLower 5 2, .triangle 3 0, .triangle 1 0, .triangle 19 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle fb04dd90357ba5d37ad3c99f71ab9d4297664e36d336808ded6235a62ac50c4f; original global index 19591.
def localCycle00108 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 3, .distance 3 4, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 10 0, .triangle 9 0, .triangle 19 0, .gapLower 3 0]

-- Original cycle fdd945d3225b765b1e16b19940617bbb13db6536700512c7606bd205dd5737a0; original global index 19841.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .distance 1 5, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 29 0, .triangle 28 0, .triangle 22 2, .triangle 3 0, .triangle 2 0, .triangle 16 1, .triangle 15 0, .gapLower 3 0]

def library : Library := fun id => if id < 55 then (if id < 27 then (if id < 13 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))))) else (if id < 20 then (if id < 16 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none))) else (if id < 18 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)))) else (if id < 23 then (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none))) else (if id < 25 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))))) else (if id < 41 then (if id < 34 then (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 32 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)))) else (if id < 37 then (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))) else (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))))) else (if id < 48 then (if id < 44 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 46 then (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none)) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)))) else (if id < 51 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id = 50 then some localCycle00050 else none))) else (if id < 53 then (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none)) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))))))) else (if id < 82 then (if id < 68 then (if id < 61 then (if id < 58 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)))) else (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))))) else (if id < 75 then (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))) else (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))))) else (if id < 96 then (if id < 89 then (if id < 85 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))) else (if id < 87 then (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)))) else (if id < 92 then (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none))) else (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))))) else (if id < 103 then (if id < 99 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none))) else (if id < 101 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)) else (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)))) else (if id < 106 then (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none))) else (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![2, 3, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 6, 5, 3, 2], ![0, 1, 6, 4, 3, 2], ![0, 1, 5, 4, 3, 2]], proof := .tail 68 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16128)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 3, 5, 6], ![1, 4, 0, 2, 5, 6], ![1, 3, 0, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 58 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16129)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 3, 5, 6], ![1, 4, 0, 2, 5, 6], ![1, 3, 0, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 3 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16130)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 3, 5, 6], ![1, 4, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 90 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16131)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 0, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 48 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16132)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 7 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16133)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 4, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 0, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 15 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16134)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 5, 3, 6], ![1, 4, 0, 5, 2, 6], ![1, 3, 0, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 74 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16135)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 5, 3, 6], ![1, 4, 0, 5, 2, 6], ![1, 3, 0, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 95 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16136)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 4, 3, 6], ![1, 4, 0, 5, 2, 6], ![1, 3, 0, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 82 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16137)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 5, 6, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 97 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16138)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 5, 6, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 78 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16139)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 6, 5, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 2, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 108 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16140)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 4, 5, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 6, 2, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 54 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16141)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 4, 6, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 82 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16142)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 5, 6, 4, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 5, 6, 2], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 28 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16143)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 5, 6, 2], ![0, 1, 3, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 21 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16144)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 0, 6, 5, 2], ![0, 1, 3, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 10 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16145)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 4, 6, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 2, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 72 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16146)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 4, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 72 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16147)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 0, 6, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 3, 4, 2]], proof := .tail 101 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16148)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 1, 0, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 49 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16149)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 1, 0, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 57 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16150)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 11 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16151)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 47 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16152)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 66 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16153)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 6, 4, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 5 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16154)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 0, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 13 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16155)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 0, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 107 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16156)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 5, 4, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 0, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 36 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16157)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 29 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16158)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 43 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16159)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 6, 5, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 2, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 41 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16160)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 6, 4, 5, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 6, 2, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 84 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16161)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 5, 4, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 5, 2, 6], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 36 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16162)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 5, 6, 4, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 5, 6, 2], ![0, 1, 3, 4, 2, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 14 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16163)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 5, 6, 2], ![0, 1, 3, 4, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 46 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16164)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 0, 6, 5, 2], ![0, 1, 3, 6, 4, 2], ![0, 1, 3, 5, 4, 2]], proof := .tail 30 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16165)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 4, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 35 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16166)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 6, 4, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 35 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16167)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 4, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 0, 6, 5, 4, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 0, 6, 5, 2], ![0, 1, 6, 3, 4, 2], ![0, 1, 5, 3, 4, 2]], proof := .tail 20 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16168)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 3, 5, 6], ![1, 4, 0, 2, 5, 6], ![1, 3, 2, 0, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 31 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16169)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 5, 3, 6], ![1, 4, 0, 5, 2, 6], ![1, 3, 2, 0, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 38 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16170)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 5, 6, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 2, 0, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 19 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16171)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 3, 5, 6], ![1, 4, 0, 2, 5, 6], ![1, 3, 2, 0, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 92 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16172)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 3, 5, 6], ![1, 4, 0, 2, 6, 5], ![1, 3, 2, 0, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 73 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16173)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 3, 6, 5], ![1, 4, 0, 2, 6, 5], ![1, 3, 2, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 71 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16174)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 6, 3, 5], ![1, 4, 0, 6, 2, 5], ![1, 3, 2, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 55 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16175)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 5, 3, 6], ![1, 4, 0, 5, 2, 6], ![1, 3, 2, 0, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 89 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16176)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 5, 6, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 2, 0, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 104 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16177)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 6, 5, 3], ![1, 4, 0, 5, 6, 2], ![1, 3, 2, 0, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 59 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16178)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 0, 6, 5, 3], ![1, 4, 0, 6, 5, 2], ![1, 3, 2, 0, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 75 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16179)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 1, 2, 0, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 83 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16180)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 2, 0, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 13 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16181)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 2, 0, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 29 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16182)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 1, 2, 0, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 92 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16183)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 3, 5, 6], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 73 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16184)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 1, 2, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 71 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16185)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 1, 2, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 66 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16186)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 1, 2, 0, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 91 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16187)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 2, 0, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 91 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16188)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 6, 5, 3], ![4, 1, 0, 5, 6, 2], ![3, 1, 2, 0, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 41 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16189)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 1, 2, 0, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 35 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16190)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 2, 1, 0, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 99 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16191)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 2, 1, 0, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 98 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16192)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 2, 1, 0, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 100 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16193)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 3, 5, 6], ![4, 1, 0, 2, 5, 6], ![3, 2, 1, 0, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 32 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16194)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 3, 5, 6], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 105 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16195)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 3, 6, 5], ![4, 1, 0, 2, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 34 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16196)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 6, 3, 5], ![4, 1, 0, 6, 2, 5], ![3, 2, 1, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 56 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16197)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 5, 3, 6], ![4, 1, 0, 5, 2, 6], ![3, 2, 1, 0, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 80 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16198)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 5, 6, 3], ![4, 1, 0, 5, 6, 2], ![3, 2, 1, 0, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 32 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16199)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 6, 5, 3], ![4, 1, 0, 5, 6, 2], ![3, 2, 1, 0, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 1 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16200)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![4, 2, 3, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 0, 6, 5, 3], ![4, 1, 0, 6, 5, 2], ![3, 2, 1, 0, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 9 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16201)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 5, 6], ![1, 2, 0, 4, 5, 6], ![1, 0, 2, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 106 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16202)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 5, 6], ![1, 2, 0, 5, 4, 6], ![1, 0, 2, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 60 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16203)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 5, 6], ![1, 2, 0, 5, 6, 4], ![1, 0, 2, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 44 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16204)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 5, 4, 6], ![1, 2, 0, 5, 4, 6], ![1, 0, 5, 2, 3, 6], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 76 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16205)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 5, 4, 6], ![1, 2, 0, 5, 6, 4], ![1, 0, 5, 2, 6, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 52 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16206)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 70 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16207)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 4, 5, 6], ![1, 2, 0, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 18 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16208)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 5, 4, 6], ![1, 2, 0, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 93 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16209)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 5, 6, 4], ![1, 2, 0, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 102 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16210)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 4, 0, 5, 6], ![1, 2, 3, 0, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 65 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16211)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 3, 0, 5, 6], ![1, 4, 2, 0, 5, 6], ![1, 3, 2, 0, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16212)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 3, 0, 5, 6], ![4, 1, 2, 0, 5, 6], ![3, 1, 2, 0, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 51 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16213)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 3, 0, 5, 6], ![4, 1, 2, 0, 5, 6], ![3, 2, 1, 0, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 40 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16214)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 5, 6], ![1, 2, 0, 4, 5, 6], ![1, 0, 2, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 8 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16215)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 4, 5, 6], ![1, 2, 0, 3, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 12 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16216)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 4, 0, 5, 6], ![1, 2, 3, 0, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 64 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16217)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 3, 0, 5, 6], ![1, 4, 2, 0, 5, 6], ![1, 3, 2, 0, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 4 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16218)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 3, 0, 5, 6], ![4, 1, 2, 0, 5, 6], ![3, 1, 2, 0, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 26 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16219)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 3, 0, 5, 6], ![4, 1, 2, 0, 5, 6], ![3, 2, 1, 0, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 17 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16220)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 5, 6], ![1, 2, 0, 6, 5, 4], ![1, 0, 2, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 67 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16221)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 5, 4, 6], ![1, 2, 0, 6, 5, 4], ![1, 0, 5, 2, 6, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 61 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16222)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 5, 6, 4], ![1, 2, 0, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 2, 6, 3], ![0, 1, 4, 2, 5, 3]], proof := .tail 45 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16223)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 5, 6, 3], ![0, 1, 2, 4, 6, 3], ![0, 1, 2, 4, 5, 3]], proof := .tail 79 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16224)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 5, 6], ![1, 2, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 25 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16225)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 5, 6], ![1, 2, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 53 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16226)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 5, 6], ![1, 2, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 103 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16227)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 87 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16228)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 4, 3]], proof := .tail 39 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16229)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![0, 1, 2, 6, 4, 3], ![0, 1, 2, 5, 4, 3]], proof := .tail 6 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16230)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 5, 6], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 96 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16231)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 3, 0, 5, 6], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 62 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16232)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 3, 0, 5, 6], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 23 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16233)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 3, 0, 5, 6], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 94 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16234)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 6, 2, 3], ![0, 1, 4, 5, 2, 3]], proof := .tail 37 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16235)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 0, 2, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 24 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16236)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 0, 2, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 53 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16237)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 4, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 0, 2, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 103 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16238)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 4, 5], ![1, 0, 6, 2, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 4, 2, 3]], proof := .tail 22 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16239)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 6, 4, 5], ![1, 2, 0, 6, 5, 4], ![1, 0, 6, 2, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 69 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16240)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 4], ![1, 0, 6, 5, 2, 3], ![0, 1, 6, 4, 2, 3], ![0, 1, 5, 4, 2, 3]], proof := .tail 2 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16241)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 33 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16242)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 4, 3]], proof := .tail 39 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16243)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 5, 4], ![1, 2, 0, 6, 5, 3], ![0, 1, 6, 2, 4, 3], ![0, 1, 5, 2, 4, 3]], proof := .tail 6 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16244)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 3, 4, 0, 6, 5], ![1, 2, 4, 0, 6, 5], ![1, 2, 3, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 27 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16245)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 3, 4, 0, 5, 6], ![1, 4, 3, 0, 6, 5], ![1, 4, 2, 0, 6, 5], ![1, 3, 2, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 85 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16246)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![2, 4, 3, 0, 5, 6], ![1, 4, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 1, 2, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 50 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16247)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![4, 3, 2, 1, 5, 6], ![4, 2, 3, 0, 5, 6], ![4, 1, 3, 0, 6, 5], ![4, 1, 2, 0, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 0 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16248)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![3, 2, 4, 0, 5, 6], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 4, 5, 6], ![1, 0, 2, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 77 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16249)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![3, 2, 4, 0, 5, 6], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 5, 4, 6], ![1, 0, 2, 5, 3, 6], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 63 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16250)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![3, 2, 4, 0, 5, 6], ![3, 1, 0, 4, 5, 6], ![2, 1, 0, 5, 6, 4], ![1, 0, 2, 5, 6, 3], ![0, 1, 2, 4, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 86 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16251)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![3, 2, 4, 0, 5, 6], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 4, 6], ![1, 0, 5, 2, 3, 6], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 16 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16252)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![3, 2, 4, 0, 5, 6], ![3, 1, 0, 5, 4, 6], ![2, 1, 0, 5, 6, 4], ![1, 0, 5, 2, 6, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 2, 4, 3, 5]], proof := .tail 109 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16253)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![3, 2, 4, 1, 5, 6], ![3, 2, 4, 0, 5, 6], ![3, 1, 0, 5, 6, 4], ![2, 1, 0, 5, 6, 4], ![1, 0, 5, 6, 2, 3], ![0, 1, 4, 2, 3, 6], ![0, 1, 4, 2, 3, 5]], proof := .tail 42 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16254)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![3, 4, 2, 1, 5, 6], ![3, 2, 4, 0, 5, 6], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 4, 5, 6], ![1, 2, 0, 3, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 88 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 16255)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (16128 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 16128 ≤ id.val) (hhigh : id.val < 16256) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 16128)) = true := by
  let j : Fin 128 := ⟨id.val - 16128, by omega⟩
  have hsum : 16128 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (16128 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard126
