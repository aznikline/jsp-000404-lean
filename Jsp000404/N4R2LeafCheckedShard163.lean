import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard163
open N4R2RowDataReplay

-- Original cycle 000f49d7e18f9d0c1459be9e5548a3825bed51e92546704874de034984a8adea; original global index 7.
def localCycle00000 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 14 1]

-- Original cycle 010d1605e7d0885f1e3e0c6cb882b1d81060a4b40e69b61ef9c2c47899325d92; original global index 92.
def localCycle00001 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .gapLower 6 3, .triangle 11 1]

-- Original cycle 01be66e2d7e35f5e01dcbcebe609947e14dba749441d7846c30b50adabdcadff; original global index 140.
def localCycle00002 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 02f09107c275e7145c31b21e3d52fe3b4041c02d8dda75690229d19dafa4ca95; original global index 236.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 04dd7e7b857d868b69c551de56f704ab72a01d1391153a6fef2a3b4224688339; original global index 391.
def localCycle00004 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 11 1]

-- Original cycle 04f8a070546a661c3a6747977df2a4587661e83b46fae451efd2b4e502f21edc; original global index 396.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 6 3, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 0621e8cf7a8900272f5de07d1c6f9330d9570b5e8345a1b9463454cadf508ba0; original global index 506.
def localCycle00006 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -3, 3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 06a24465f2cc7199dc48e92b47798e638731fc38a389af4d877ec5083eccc496; original global index 546.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 14 1, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 06bf8d79ee3643eac2873f40357a04ad5eca36501303e041b461dcea566482e1; original global index 554.
def localCycle00008 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 06effdc7899f3c03831c63ef21e11417e45020f464c170d82ff9b96bb6c80702; original global index 569.
def localCycle00009 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 089bb546a0d31aaa0b67932670fd4d881fbeff6a233c6e866b5258ef3d304dce; original global index 685.
def localCycle00010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -2, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 30 1, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle 092542769fa3337a1b5e754c18bc0a0a23a722443ae5e96dc5892bafb65d1945; original global index 730.
def localCycle00011 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 092e7a3461a55e47cfe3ba518977943b58a6c3846e7d95095ba95138d0d6514e; original global index 735.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 09def4a0ea27eb902dea0e5eb202f4254decac5b95290364287cafbf62e54cfb; original global index 796.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 0b3943b63bdd84adf2531174d354404678ae0f891c1f388b9ae0015071ef84f2; original global index 898.
def localCycle00014 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 4, .distance 4 6, .distance 3 6, .distance 3 4]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 4, .gapLower 6 5, .triangle 32 1]

-- Original cycle 0d2ae12ec9101b98d2b8cf1bea31fa2cbe40208a8646140d7e2c0913d178193e; original global index 1046.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 109d70dae844bce971c895d624f89a9343f74ce567e1a48583c72a276adb1090; original global index 1334.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 12a253583dc38155c142b2be545f597f7764f5cbcde1419ae45ca52a6aa3914a; original global index 1473.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .gapLower 6 4, .triangle 11 1, .triangle 10 0, .triangle 20 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 13b24dbb2cdd745346dc1245bdf7015f0640ed1d690b450b021e006b7e2b444e; original global index 1558.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 3, .triangle 18 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 153780049cd1bd3f844f2f072b8760803541cfddc5d23d9c1e7d5509a052b8b5; original global index 1679.
def localCycle00019 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 3, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 15ecdda9ea9a91e388d572012dbdf5a059f2b28c9666c481fe7285b9b89f1366; original global index 1739.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 16420727fde9801009558d494b45859374d9aca618547125b8e4afc781f10b92; original global index 1754.
def localCycle00021 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 0, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 17891415f85b4d56579c7d5e14ace93073918688b0c5a9a6efbca29f91232259; original global index 1840.
def localCycle00022 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 17d5579bbd60659f2ec2107d5e095f6f6145d57abd6eeb09128707af07134653; original global index 1862.
def localCycle00023 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 185bd44b83969a15cc9f3849531d796e0f0929418fe0bba6d5d57c15cddc2a45; original global index 1908.
def localCycle00024 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 19b1f8a16adf507348ec91368930473913f9ccf730679da2f5b4e99eda77b63a; original global index 2007.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 19e265959ac78f8afca68981daf06f0669732f9ec597692cbb545bd8b343fcee; original global index 2020.
def localCycle00026 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, -1, 0, -2, 3, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 2, .gapLower 6 4, .triangle 11 1, .triangle 10 0, .triangle 20 0, .corridorLower 1 3]

-- Original cycle 1a391bb1f9ae345c99abc9b0cc9b75075eeafdcc346b8d0623852adce9eade63; original global index 2050.
def localCycle00027 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 1c6fe2cd70f3b5bc03609116cba56ba226bdadf9530ce4d57aef0732609f4129; original global index 2182.
def localCycle00028 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .triangle 4 1, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 1dfc93c0235044470553e23319c5c5051ec2d148540f5bb4c98a912fa174a9e4; original global index 2305.
def localCycle00029 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 1f35ddb562819c41d5c95585151c31e2275f966544f77b917d03611517577f1a; original global index 2395.
def localCycle00030 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 21 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 2134c846625c4ec32eb9e18ea375aa4bba98f9314fda48ff1f2511ba9a55170d; original global index 2545.
def localCycle00031 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 2137044fef7ac9bcbdd4757c6178d57d8f125a0b3800dbc842bc0e5d0158fa6d; original global index 2546.
def localCycle00032 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 21766cdd929a0fd5e316138034ef33dd4b3cbb6fde8573dc59f9ff67a7acdf21; original global index 2562.
def localCycle00033 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 5 6, .distance 1 6, .distance 1 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 6 1, .triangle 24 1]

-- Original cycle 2474f9fc0570c5be5024a91a2d387ad6d94d7c81428cb6e6aed11c06a32a4516; original global index 2796.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 0]

-- Original cycle 24a6fbf2863b6b6a4471a833bbb4c5fcede3347f77d8333f4268946df7861618; original global index 2812.
def localCycle00035 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .triangle 4 1, .gapLower 6 2, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 2599a86d7a075e0d205d5d4266519f382bfe14823b5d84385bbe1aa04a2520ef; original global index 2890.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 263463611f9fce1b7c1c208286ab7166d456f3313f7d8ac3e0a16b8ed9a1de7a; original global index 2929.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 26ad513055ed85106e154f0a8b0b56e63b7e71b755f7defceecafd4c9c550b7b; original global index 2964.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 2704620bf03253aafba9fec85b824bac73a7501fa44627c57eda9db9dc3123ba; original global index 2992.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 278df901e175512c8d1bae884dc6c3ce2e76161436de3d5cc52db5d00fd26fb5; original global index 3025.
def localCycle00040 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -2, -2, 0, 3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 298d47f08bfc2fbf776738a93c74fbbf140d235108b9a10723581bc85ca01198; original global index 3169.
def localCycle00041 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 2a41f9067e5f9db70bbaa25d00ed392488a12a63de97287151354518a5ee3394; original global index 3218.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2a95d206e9f9172b3622fc10ad7fa1d0a8afbd8bd5987248feb914ca347b8110; original global index 3240.
def localCycle00043 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 2bcbb94b68800bf5c2f2506224ab866f1aea5b85e420fd8cdcf38a6f9acdc35d; original global index 3349.
def localCycle00044 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 6 3, .triangle 18 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2d3fc4530e2201afcc31dde8026bdcb31dfdecae6c33f1330fbe31f66da6e645; original global index 3454.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 0 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 13 2, .gapLower 6 2, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0, .thetaLower 0]

-- Original cycle 2e25a51613dcd9c39401b807d14bea5793952aedd03fbb7212199a51abdd1756; original global index 3525.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 2e46a0e0d8f1d0eaad9e0c780d2a64107645cb159b10f41e7c812dba6090f12f; original global index 3540.
def localCycle00047 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 2ecdcf9c4e0e507bd51b46d0d28b2c16e3b1757be9b33064845860c9613b272f; original global index 3582.
def localCycle00048 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 11 2, .triangle 14 1]

-- Original cycle 2f21ff58d33f74a8ae10865437877b9d406b02a56bc91f2c39d54eff91543ab3; original global index 3604.
def localCycle00049 : Cycle where
  length := 7
  data := {
    node := ![.theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 6]
    constant := ![3, 0, 0, 0, -2, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false] }
  origin := ![.corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .triangle 23 1, .gapLower 6 0]

-- Original cycle 2fb53cf6a6d117c13c8da9dc875c19a9c0b3d08465af995a474fb83afa1c6bba; original global index 3647.
def localCycle00050 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 1, -2, 0, 3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapUpper 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 302d4e1fd179a76155299b683bc247ad5dd229cb8016fe28ee6da36c104efde3; original global index 3670.
def localCycle00051 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.triangle 8 0, .gapLower 6 2, .gapUpper 5 2, .triangle 7 1]

-- Original cycle 30e7d430e2ca1b5058f3a171d2934a5fd8a79be964c0edee2480bfa2192a1c03; original global index 3730.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 31e8693eaa1d1f01b1f137b5cada1f69f11a711a609b96597a0609cf652d307b; original global index 3809.
def localCycle00053 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .gapLower 6 3, .triangle 18 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 3390e2f074fb509cc86bdbe715258eb7b4d272672baae2e03652bcd42382ab72; original global index 3946.
def localCycle00054 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 349fb1d171fca56a40b313b0c80d7be80e4aadb21015dbfcc3e126e5f5ead8c9; original global index 4028.
def localCycle00055 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 8 2, .triangle 14 1]

-- Original cycle 36050ed86f902da8ec49c2f33cd6d515018a975a4ab37b9bfc6021d005acc4f9; original global index 4147.
def localCycle00056 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 37dda53311bac901a8b1e92de4ab72a54607cc6b4c692aa2c24fb19457854d3b; original global index 4293.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .corridorLower 1 3, .thetaNext 0, .thetaLower 0]

-- Original cycle 38611d3fac1a615763294e62a8c4017c888915d783989ca4b3e6c7d34e4ebdca; original global index 4336.
def localCycle00058 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .gapLower 3 0]

-- Original cycle 38b8773370faa216b90e9f1f383bfd9736b4030612db20d7563f07f792283c66; original global index 4364.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 21 2, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 3af03ba2a6cabd39b62aa2ff5dae6e7eeddf32f806bc93e410314973c3f6b233; original global index 4550.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 4, .triangle 21 2, .triangle 23 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 3d461a205e337bcfa20e2177a664fb6b6bc6133473c34ee3f8b8708eb1456582; original global index 4746.
def localCycle00061 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 41c35ca03354de2300af17734aec6ceeac3b0a1891e1a96f98e5ec90e10f136b; original global index 5074.
def localCycle00062 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 15 0, .triangle 26 0, .triangle 31 1, .gapUpper 4 1, .triangle 16 1]

-- Original cycle 424e8413cd3a008f177fcbb1dbc7713f47b0e750d9710335d1e7e9c0963e94f2; original global index 5107.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 22 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 435cf4976ba35ebdda3488007aed026c53a03594a2a18fbd1e72e3e3e97656ea; original global index 5199.
def localCycle00064 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 29 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 46d70da64e4ca6be6d74479aac48f6e4c3084fcefdfb9e90325215d6142f9108; original global index 5489.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 11 1, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 46dbeeed75f6a7ed78b23f5a37d09cbaa9c7f2aad98d8a620d0257e4b998ac5c; original global index 5492.
def localCycle00066 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![0, -2, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, true, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .triangle 30 1, .gapUpper 5 2, .triangle 7 1]

-- Original cycle 48f75ce231cfb372c91bd59f18c32ed3ea5304cad027d520a2b2ab0ff4f8e75f; original global index 5649.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 492b0c150869277a440de2d3e94ae5a66862b8f77240c2edcb861dd166c81149; original global index 5666.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 49f7b2d0bbd282cd0dbf81c1a0b29e567c2921ef86669abb84b8c57fe5bd43b5; original global index 5743.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 4, .gapLower 6 3, .triangle 18 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 4c6e8d3762586620e1d37a3bd3593c8950063b6e37c573c8cd40d21c37d15160; original global index 5935.
def localCycle00070 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, -2, -2, 0, 0, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .corridorLower 1 3]

-- Original cycle 4d9f9738b1310ee9ed9caa28383ae2562d33fdbe9985659a6c9c0c65ac1a2be3; original global index 6030.
def localCycle00071 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .gapLower 6 3, .triangle 18 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 4eb5996c08250868c000c1e2601286c1b3736a2c84c08544ba0e332a0030b38a; original global index 6118.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -3, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 4ec0832cb212179cb7a0f8bebc40e981431613994555e92557de7c313de0b311; original global index 6120.
def localCycle00073 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 3, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 4ec5e2e5c33d4fd6b0bd57be401e4990693baedaf40f749631f93d1dda927661; original global index 6121.
def localCycle00074 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 4fb6edf5c20d2771e5c0fe364d38c83cce9d0976bdae39be84d58a6110455a75; original global index 6190.
def localCycle00075 : Cycle where
  length := 3
  data := {
    node := ![.theta 5, .distance 5 6, .theta 6, .theta 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 0, .gapLower 6 0, .thetaNext 5]

-- Original cycle 52ab866aacf7887e45da17144cde3b1fd5cc895ebb61c59e33dbfd44a174f98c; original global index 6425.
def localCycle00076 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 52b8598a3c7bcc409b449e30c9968ece43a67bf1d164e7476070afc57d7e9ad2; original global index 6432.
def localCycle00077 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -2, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5358d3f0c1d40940195dc29cf2298e912943720e8ce4e4d0797ad477d4b8c1de; original global index 6482.
def localCycle00078 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .corridorLower 1 3]

-- Original cycle 56d56bd34aac9776849ef085dbad3ad33012ff23f26f9c9bfd20c4cf9c56cfc0; original global index 6732.
def localCycle00079 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -2, 0, -1, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 588bb0a820c6449cf7e72852510632c0988394365186d303d4bf134312fd0bd4; original global index 6872.
def localCycle00080 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 0, 3, 0, 0, -2, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 592644e432b785d579a371e99440e709a4e50a407eb95656b91bba05f52ef5f3; original global index 6912.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 5bdd3d14d24b6c89a2840626057e0ddca459cbadad5da54f6d5ae2a504f5e9ef; original global index 7141.
def localCycle00082 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5d234ea86954474770a682ce08ca2294dc0e97df4e45843d6bd83c9d53322869; original global index 7249.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 2, .triangle 11 0, .triangle 10 0, .triangle 20 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 5e0b037f97b1c46a0ff87608ff8d08285e641a3fdc22aa194bb1341679461e9f; original global index 7314.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, 0, -2, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 5f0f2431a3f805fffcf2f93fb846599ca610e72f1d28aed708aa4e29f5397af7; original global index 7402.
def localCycle00085 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 5f362bbcfd88c7c1ab16d9b497216b0f941ebbc5fbaddcb6c7445cf8010cdae9; original global index 7413.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 5f974b5b2bc7cdc0023e0a820d798ca0ccf321705c9c310b17562d9c9e5a7f95; original global index 7444.
def localCycle00087 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 6, .distance 1 6, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -3, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 2, .gapLower 6 2, .triangle 18 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 5fe1dabdd9f8b04f57eddc95c5536879813b30ed23c7906243c3ce0c189d7d5c; original global index 7474.
def localCycle00088 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 60bed6256c79f75d2c3404c8a72dc27ed045ee2b736ce1d429391d8b319f56db; original global index 7534.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 6369a3d6e0f83397e18379cab37df680c33597a04fa7447f564a1ba76d676487; original global index 7757.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 652172eb6ed5f40aaa0e6b0105ac9f67f7b5098e54c8c1fe8d6c0f23d86fa99d; original global index 7869.
def localCycle00091 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 0 2]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 5 2, .gapUpper 3 4, .gapLower 6 4, .triangle 8 0]

-- Original cycle 6718291500195620a22047753c703ecbe62615848279b192cc59bd4e5fa173b4; original global index 8013.
def localCycle00092 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 15 0, .triangle 27 0, .triangle 32 1, .gapUpper 4 2, .triangle 16 1]

-- Original cycle 67c2b64a537a3b7e74bdcbffa4ef37f86658e2001a6f01cbd650fd50804a70b6; original global index 8059.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 67cd5fee767690ea3abfe3e14ff62b423db71b847efc56045c01d1201f4a4256; original global index 8066.
def localCycle00094 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 6837905f812d15c047e199d09522a49aebfb21f5ada3ab0bddf2f6c8deb769d4; original global index 8103.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 8 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 6acf333a60f4713d289279c176fde67c0e8cc3c850abdd8b6163dfc91cf7a451; original global index 8315.
def localCycle00096 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 4 6, .distance 1 4]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 23 2, .gapLower 6 1, .gapUpper 4 2]

-- Original cycle 6c6d93e9f6cdfd10b807b56bbc835d63f13ed51061588c6cca73c52491230374; original global index 8441.
def localCycle00097 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 6d9d6d937684946acb2ef40ad90d53852725dd06cf8e04526eb7d4ce70ee0c97; original global index 8519.
def localCycle00098 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![4, 0, 0, -1, -1, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 5 6, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle 6e11207624036df98a9ad9de523ebc614cd73b9b71c91e6055d03740158d7722; original global index 8546.
def localCycle00099 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 6ecf11c3f5c7cc8daa6217b6e055c34f2e65f79ea0a72956c0450b517517cb8f; original global index 8598.
def localCycle00100 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 7062b2c3eef75a8a1dfa190fa5d314da6407af91473c470c1c1a84d0f03dfb4b; original global index 8706.
def localCycle00101 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 3, .triangle 18 1, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 70cc0d99ea31a31f69ce0dd2d7e54e816832dfb0acd96fc29b583ed7f05f6928; original global index 8742.
def localCycle00102 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 70ea68d6267f9f1c306a1fc29bfe5f265918c68e6c3693f388a3099a40592f89; original global index 8752.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -2, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 1, .triangle 30 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 71687360070439957e07f75c35309d1ae88e7e9bc435ddbb70387b462f5aea05; original global index 8799.
def localCycle00104 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 2, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 0, .gapLower 6 0, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle 72a8c2d617e2e2c0a1195c66e1051727ce3d2eb1feb3f9516111f107cc22c073; original global index 8877.
def localCycle00105 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 73510f3f7151d630fe3f1b4e1e3334d20a7accb694658a8f09be7cd4ce7b3ae8; original global index 8926.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 75408cecf1306eeb51b538ffdc0971b4d2afcaf30c123bc31b1e07acd3adeacb; original global index 9085.
def localCycle00107 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 0 3]
    constant := ![0, 2, -2, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, true, false, false] }
  origin := ![.triangle 10 2, .gapUpper 5 5, .gapLower 6 5, .triangle 11 0]

-- Original cycle 75739cd92cab188eeb06e104f07c5327d7559751805d289deaa539c2ccaab20c; original global index 9102.
def localCycle00108 : Cycle where
  length := 6
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 33 0, .triangle 20 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 76a01646724524afa85a0db791a9adf18ead756b4e95158815454b65a23efc80; original global index 9180.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 78c78e7b32a5f0593af93465859abbc1971454cc31e89665adb047530ef7e26f; original global index 9346.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Original cycle 798418b98b19bb18b6ea075d7c4165c7cecc8861672457d18ff5eb2b84625e5e; original global index 9400.
def localCycle00111 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 79e0c2a1076d94eff68a5fea8a7e6dd99c8462bf0a10f4907fba59d90ec6f9ad; original global index 9426.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7bffaabb34ab9289046255238b1de7612d58001534dc8a091db9e2135b2aa79b; original global index 9591.
def localCycle00113 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 7c333b7994d2fd9b325d5b2f5a9750165dfcd9bdd6429a0ec95832fc46a85bbd; original global index 9615.
def localCycle00114 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 7d7860e877a3d6df0c2a2c73e562c61b2db0ba4f2b7e75ac292a009dfc79a942; original global index 9729.
def localCycle00115 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3]
    constant := ![2, -3, 0, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, true, true] }
  origin := ![.gapUpper 3 4, .gapLower 6 4, .triangle 8 2, .triangle 11 1]

-- Original cycle 7e5d957ad83f3c6f02f128e1b2635929dd11d7d36129e51e1e41c4fc6fffc1b1; original global index 9815.
def localCycle00116 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 0 6, .distance 0 2]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 6 3, .triangle 8 1]

-- Original cycle 7e98c7fa4ab072ca32ed3c2194935953be148d98a6c53c177dea915ab279b1fd; original global index 9829.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 7ee90ee14ff66d2993b1211175dfdd35a3d2bec4f959b17fac254fd7e8b0518d; original global index 9854.
def localCycle00118 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 1, .triangle 18 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 80135b6639ad683150d3de259a9f1b5b009269c094d11a4aa6a2bd888663076f; original global index 9934.
def localCycle00119 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 801fa73d78e92194e96e55980c6a3b23568bcc5fa0f5a7536e889f37ca7137d7; original global index 9938.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 2, .gapLower 6 2, .triangle 23 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Original cycle 8118c3a5f7852ea01a6336b87b4160f904a12d9f394bdf1d570efef26cef7e84; original global index 10018.
def localCycle00121 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .gapLower 3 0]

-- Original cycle 8426bcfdd7ba816baa3471f9771ab7c6b49ef8d68a445a80cba4cb5c95d93346; original global index 10259.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 84507fdfc3155f8f3286cdeadad8293647e75a02fa75d563b7756adca330ccc2; original global index 10278.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 4, .triangle 21 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle 8595923d5d85993aff1e51790c1e0292423a8d38212a0e2ae38dbddb8b3e9937; original global index 10367.
def localCycle00124 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle 85beadd09ce5d1e845a18842d00d133151387994901b4056bbe07a5ea7d1a11b; original global index 10380.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 85d440dda3e33274d8f683db65257288fcdfbf3069a37a3f5ebea0ccb75af89a; original global index 10387.
def localCycle00126 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 8642f1ba0bb5d96f897c8d393b6da372437b0ac8f4bdf3b02d51ac6a0e88a952; original global index 10410.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Original cycle 867267ae1d3e360ed5d55b9e577b10c56a5b3773d1303c581a713b36a72c7657; original global index 10425.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 8a505ed99eaa37a1c0a0a1ac25c5956f79f92cfb15dd7f1e2285a5bbcdd564a7; original global index 10718.
def localCycle00129 : Cycle where
  length := 6
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 8c94eac1cf3b43318b95a5586af0c3ad8bd4a12c7281081a1f53d6b794a86ef1; original global index 10875.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 8d763242ce855515b0ecee9013f6d71c51963a7993fd7d8550880d6650eed290; original global index 10937.
def localCycle00131 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 8d929fed4de0182ee49ec1e3935fcfb7de72263c3affd858f04f882d2360b2d0; original global index 10946.
def localCycle00132 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 4, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 8e8e26f5231900cabb0a59829e30fe7c0ebea3d0563b1fc8d6609d7c4a14236b; original global index 11031.
def localCycle00133 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 6, .distance 1 6, .distance 4 6, .theta 4]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .gapLower 6 3, .triangle 4 1, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 90adce4599c6feab7cad3406500f5d5a9ab1de06f001deebfc67574b7bb745f5; original global index 11204.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 90b8f82100c56db633072360ea6832a8d3076f02333f079e19ce2b0c96b5d425; original global index 11206.
def localCycle00135 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 11 0, .triangle 27 2, .gapLower 6 1, .corridorLower 4 6]

-- Original cycle 916d0c8569c7e071ecac3deea6949edb458dbe9b74a14e0153cdde3c48038a13; original global index 11265.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle 9293dd3b53a59cfc038b1e73800fec37158132145a04f1aef29d8c895018a862; original global index 11356.
def localCycle00137 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle 94c848c021bd469ade212c271ae1ae5ecdd58f1d68668bae154d66e23fbd5f5d; original global index 11547.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle 9512131260e128cf79859c536e14ba7b6508e9839bde18a4e50a26321c02b274; original global index 11578.
def localCycle00139 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -2, 2, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .gapLower 6 6, .triangle 30 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 20 0, .corridorLower 1 3]

-- Original cycle 95e6d4db26213caece4f981864b7365c2abd1cfd1376a141e26aab44607c85a9; original global index 11654.
def localCycle00140 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 96f62cfc87a2ee89d8cf955a6e6c8f7341ee05cae48a3eaf8b43fd344b9a2979; original global index 11734.
def localCycle00141 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .theta 6, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![3, -1, -1, -2, 3, 0, 0, -2, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .gapLower 6 0, .corridorUpper 5 6, .triangle 33 2, .triangle 27 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 20 0, .corridorLower 1 3]

-- Original cycle 973e01c26f0731750b818e4397b55b22887aa1c8eefa2b24773b9c4f16aae6bb; original global index 11753.
def localCycle00142 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 97fb3e7e62fdc524ad198efa66299ed69e6cc1c7689933ad0f3353e823f61765; original global index 11803.
def localCycle00143 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 98e31f0d6d56a0e66779bb13b451c5870fe953b20823d5d013fb917394a8a86a; original global index 11870.
def localCycle00144 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle 9a737df99cf76b529b5d27799ad1373f4ef68a5ef1cdffa62f617fc21f762705; original global index 12000.
def localCycle00145 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 0 6, .distance 0 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 14 1]

-- Original cycle 9ab101ecb0155443db42908a20a0b708f26cdcff4326c9354fcf3d21f8dad6da; original global index 12021.
def localCycle00146 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, -1, 0, -3, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 0, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle 9b8f09496d07c7c0a0dd3c49d97cc19c6064ad4a9434591a067bdaaf2aab40e0; original global index 12099.
def localCycle00147 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle 9c87cdaecfbea10d67e9ec69b625be28b6d33c6f0e3287fbe53682cf98f85419; original global index 12173.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 14 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle 9cdb6af4496a11cb8bddc5129a3af47e7e7d6d2f4672ac142e5ecc14eaa55999; original global index 12200.
def localCycle00149 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle 9d2a466919f12d12352f45b10965f9252cc89edf15e1d8abc23f375cfdcb25c8; original global index 12226.
def localCycle00150 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 9e63b68b91649d67792b16e304f31d2166cf55a47b793432a826cfab76b0d47f; original global index 12333.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a07627135ddc97c8910ac19eebca9c0a50d6b8f3d9574587180f82961317fae5; original global index 12486.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -3, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle a140b1d76f7ee24d4b6d22836b81c5011cddba96d05aabda0b564a302c0cf928; original global index 12538.
def localCycle00153 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a21ab71a4b6ed27e13dee017f49378bec53ae4908c829aab6b49a4b4e0af7846; original global index 12611.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle a4bc43305e2ba0f44162142be428be60fafdf4bff2a80d57473da1c056b1997d; original global index 12803.
def localCycle00155 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Original cycle a5eb27bd2745e04158feec9470e78d100e90c700484462a27f17ed56fc319c87; original global index 12890.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle a65682a936e3d06ad8d81440149525f852b14d5a9b44995a9befd83d0ef98ffc; original global index 12922.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -2, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2, .gapLower 6 2, .triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle a6fbdd6c9fc7bc1ec4aee38adfef2ff525acf41e5bfdb3122a29aa189a838489; original global index 12978.
def localCycle00158 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 30 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle a81fab8a33fc036313c3541005dcd5028c2e61ca6bcc0a857706d4c277398afa; original global index 13092.
def localCycle00159 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle aa4926792d846d66b585ceb5e3dbd593a1ea85b63c4be831435fa5bf68859aa1; original global index 13260.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 6 3, .triangle 18 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle ae0d3e85487a3700c2f89194323281ab4f27357163cd310e32a75bdaf2626b95; original global index 13581.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, 0, -2, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle af0e3b29d1baf51da9d38c2e9a7dff04b897528abad205a4829d3e9cdd5409b3; original global index 13667.
def localCycle00162 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 4, .triangle 21 2, .gapLower 6 2, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle b14a96a85284f36770b049b38e364bf6580c84919e37d3267b86ca27af305353; original global index 13849.
def localCycle00163 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, true, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 14 1]

-- Original cycle b179f5057aabf83c5b44df1cf7eeec89571d94cf2b04dcb73218db92603733f8; original global index 13872.
def localCycle00164 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b17e7d042aca84662d08d9e2ddeae338b045cd782377031f7fb7bc9f09315982; original global index 13874.
def localCycle00165 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .gapUpper 2 4]

-- Original cycle b2a00cf25d025e2b3e4b6b9c8c92f3862e1c3f8436b63c49b245d4fa0600a6df; original global index 13961.
def localCycle00166 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle b3176aaa47c9b2e3b0f7ceb30e22ff48bce9715c2c844420fbcaa87078eca024; original global index 13994.
def localCycle00167 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle b3fc8a59439ad918d27e1723c487f0af993bae50978782fd04b19a02d5fada11; original global index 14056.
def localCycle00168 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -2, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.triangle 3 2, .triangle 14 0, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle b51e2d1853fba2fddc3fe8497297ad8df307dc7373c3ef2e957b5588516518a0; original global index 14153.
def localCycle00169 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -2, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .gapLower 6 3, .triangle 18 1, .triangle 29 1, .triangle 34 1, .gapLower 4 0]

-- Original cycle b51f7c3c4982140d7f7cd423d40272d5f1499f41966f5576ea2e3efd3824c8f1; original global index 14154.
def localCycle00170 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle b5337716f14445e9b09a7603bb119b775cbcf567329f95f8f024124eaf41e52f; original global index 14158.
def localCycle00171 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 24 2, .gapLower 6 0, .thetaNext 5]

-- Original cycle b64243a76e2fbd174532b6c936aa635bf3b3560c60dea5eaba257d9e94a83b27; original global index 14241.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .theta 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .gapLower 6 0, .thetaNext 5, .thetaNext 4]

-- Original cycle b659ed63cb1b02564354cbc3c9b6293ffe645a22aef5be8718698ea8a1211402; original global index 14251.
def localCycle00173 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle b6fd1096820ba4d7e39eec597b4babcaa56d5c8565c887240f23798129fe80ab; original global index 14292.
def localCycle00174 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 3 6, .distance 0 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -2, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 2, .gapLower 6 4, .gapLower 6 3, .triangle 18 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle b7c37d5e162be7246f34681d48534223763f8fe8b432a07bae45e9a2c36dcffa; original global index 14340.
def localCycle00175 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle b84217cec744d2e702a997fdd896b089951954f49b1f1f0fca7275e6a6f39463; original global index 14376.
def localCycle00176 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle bf34a4fcfc78362b4509ad5d6f44bed8723bb26d26bd8b3273e6e9700f893925; original global index 14924.
def localCycle00177 : Cycle where
  length := 17
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle bf79df876bfc55c1fcceb0549c0c7cd9ac22cceb8bdba7f6833840e1cb628e02; original global index 14941.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle c02b431c96d970e580e5b1d48993db1d9b6b2694c2c7597d812673f7e84cb363; original global index 15001.
def localCycle00179 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 0 6, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -2, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .gapLower 6 5, .gapLower 6 4, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle c1ed39c00dddb93e7fd8321ed53489735988d8935d53d657f550f6333f42c8fe; original global index 15142.
def localCycle00180 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 3, .distance 0 6, .distance 3 6, .distance 0 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 11 2, .gapLower 6 4, .gapUpper 3 4]

-- Original cycle c400d9b454303d293796cbaf806948f99ee9512418a532d27b147809dc6a793f; original global index 15288.
def localCycle00181 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle c497ad5125fccc60f639f129f53ce1da188495187bd851c2d67443649588513b; original global index 15331.
def localCycle00182 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 29 2, .gapLower 6 3, .triangle 8 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c797e5a0fb02de15c835b7b33db7d60202cb32434ce97cb36abecfa28edcb6c7; original global index 15576.
def localCycle00183 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle c7a0bb2205ce17b7742ecb4808da8b912a786cee9568f1f47d977231124820cd; original global index 15580.
def localCycle00184 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle c86c123c6ba8c40a1f2047d7a0ffb39635db09050688113b226f24abecedc530; original global index 15647.
def localCycle00185 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .theta 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 2, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 2, .gapLower 6 0, .gapLower 6 6, .triangle 32 2, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Original cycle c929e639d176046fb018f3deae36209d671eec1e1c667b4d3b6f4d4a3fd91b89; original global index 15720.
def localCycle00186 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 2, .distance 0 6, .distance 2 6, .distance 0 2]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 8 2, .gapLower 6 3, .gapUpper 2 4]

-- Original cycle c93faffd79901995e57e10bc58d70eecf597c9693bf76f09d16667d6ba95198e; original global index 15731.
def localCycle00187 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ca438f151831a4d01e83c7cd4a97dfcad472ef7f6ddde0d433b6f747c9dfae86; original global index 15809.
def localCycle00188 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle ca8a061bbed47eb5c653e74878c9b7064402c1f33f335bb5d3e4fc127689a276; original global index 15829.
def localCycle00189 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 5 6, .distance 1 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 6 1, .gapUpper 5 1]

-- Original cycle cb5e6872d88aad9b4545c4a4d6b165e6eda8271b33ece8f4e7ba60fefe1b9a9e; original global index 15887.
def localCycle00190 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle cef9b37065b2084193d545f5a4bed95d7934bd32e07bbf622f9e193631bb97b6; original global index 16150.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 6 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle cf392713ab4f777d35b376fcecd0dc96a616708edd5640defa4606807b9e3e26; original global index 16174.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .gapLower 6 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle d0f7cb2cd2e39b950c8043869abb3a23a05407c16f26c55771d4ee784878e888; original global index 16318.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .theta 2]
    constant := ![4, -1, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false] }
  origin := ![.gapLower 2 6, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 21 2, .gapLower 6 2, .corridorLower 2 6]

-- Original cycle d1aaedaff7a62bc0549571372ed733a236dba0b8d20ec159ed92e6787af4e20b; original global index 16364.
def localCycle00194 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle d32cae771064c5cd1d0fb8621fd98956496f4013c39a812353f2d93263e4d99d; original global index 16473.
def localCycle00195 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle d365332c0597af2daa47a6ebc682aa07b08c03f0c105f48054e1177edc01d3c6; original global index 16489.
def localCycle00196 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d3c6681dd9493a8faaba1fbd00b737d43dbb29ff6e164affa178c57196443793; original global index 16525.
def localCycle00197 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .gapLower 6 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle d6880f389683255bdb4afea9b9cfe9d6f10354b58b087a8c2555101ede6a7d42; original global index 16747.
def localCycle00198 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 32 0, .triangle 25 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle d91068ded6e9e352b5b93466a78f48002bf69f957f16f53cc504703ada4588da; original global index 16955.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle da0aec30d28c51b425e971a5d53f606f61b4069bdec7b26e13f00227a50e3d34; original global index 17038.
def localCycle00200 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Original cycle dc45670aa681f5285aa133ab43ccbafd9d9708345974106e102b9275c0c34492; original global index 17212.
def localCycle00201 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -3, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .gapLower 6 3, .triangle 18 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle dcc51955f456d92d34836d9b800c450c550609b7dbeaf14c92c5d1e4ae097a6e; original global index 17249.
def localCycle00202 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 0 6, .distance 2 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -2, 0, -2, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 11 2, .gapLower 6 3, .triangle 18 0, .corridorLower 1 2, .thetaLower 1]

-- Original cycle de2bcd906c4b6fa7a28d30f6df4ac209edda2af1ba6187d59cd6b6f2bdfecc7c; original global index 17372.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 23 1, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle dfa59f3f2e0e5849061fdeeb14e6b1c8b6eb423298711390d01ff1215bc97460; original global index 17471.
def localCycle00204 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle dfa608aca14fd809f048feb031c37f55908fe0302ceb016cd5d733f9e18697e1; original global index 17473.
def localCycle00205 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle e006fa82ee59a14be63f01d8acd803ee64add3031bd8fbb6d0dcd2978e8a0dba; original global index 17512.
def localCycle00206 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2, .gapLower 6 2, .triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle e06384b1b9d7b0011ce01ac5b5743eb626e62cebea6b338bf799a89b28b52f74; original global index 17541.
def localCycle00207 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle e2a888cf7ab45f6e36ecb0110b2f9f6765598c073023fd85cc71f199cb3bdb18; original global index 17725.
def localCycle00208 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle e36844ac09df1c214845ec8dd39aa44962ca4e1e8dcd7476eb2acaf27447eca0; original global index 17783.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle e396c96a1dd00c2cf3436c2b5c47a8f1daab4578e737678617cc3f848a9a36ee; original global index 17798.
def localCycle00210 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 0, 3, 0, -2, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Original cycle e3ccbdaa38fec994ee2e54e2e608b3df6304b29221329a803c0e21b9bc0b703b; original global index 17823.
def localCycle00211 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, -2, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .gapLower 6 5, .triangle 11 0, .triangle 10 0, .triangle 20 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle e50f15740b3a5e6e1fd5309c29e7086541cac9fca500c346f97c136eabdb547c; original global index 17906.
def localCycle00212 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 3 6, .distance 0 6, .distance 0 5]
    constant := ![2, -2, -2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![true, false, false, true] }
  origin := ![.gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .triangle 14 1]

-- Original cycle e5f72892a1667f11ff99bd8bd67ad3538f403d039b4f56a1748b67280299aa06; original global index 17993.
def localCycle00213 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -2, -2, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.triangle 3 2, .triangle 14 2, .gapLower 6 2, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle e7dd7d2eda700f3b429a22aa5b9bf45f249dac2c5906173c4808b9c3acfb1029; original global index 18132.
def localCycle00214 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Original cycle e8fb44c4f1c40d9d01f3d2f76670df4b951152e0a6f84a27fbb4cc8980452d71; original global index 18208.
def localCycle00215 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 2 6, .distance 0 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 0, 3, 0, 0, 0, -2, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 2, .gapLower 6 3, .triangle 8 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Original cycle ebccab97d7c0d7f1d94281591b5f386b3bb2a119799b30ea4783b2d0141ae48c; original global index 18399.
def localCycle00216 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle ecf6ddb9936bc7d7d7078b04e87c6983a221aeb60d667fc9ea9b1a472a8c22e9; original global index 18497.
def localCycle00217 : Cycle where
  length := 3
  data := {
    node := ![.distance 0 5, .distance 0 6, .distance 5 6, .distance 0 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 14 2, .gapLower 6 2, .gapUpper 5 2]

-- Original cycle ed77e966dfb64c8194aa2b5d10bb19fb2d47d94ee73c836dab79345d2fc7d5d7; original global index 18536.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 6, .distance 0 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -2, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 2, .gapLower 6 3, .triangle 4 1, .triangle 24 1, .corridorLower 5 6]

-- Original cycle eda6a16d245b14b8a5c0099a2f95d5025518a8f344b4e3a20e3a0c66f9d079a4; original global index 18552.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 0 6, .distance 2 6, .distance 5 6, .distance 1 5, .theta 5]
    constant := ![3, 0, 0, -3, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 8 1, .triangle 30 1, .triangle 24 0, .gapLower 5 0]

-- Original cycle f023a76b3c7a59c93bafc53291021f15e6622b1eabb096e5f8b06d7526918f81; original global index 18732.
def localCycle00220 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle f081b8963e83323f7158a2eba2f525d675d1eb7c65da54f94142ec9750a3190d; original global index 18755.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .gapLower 6 3, .triangle 18 1, .triangle 29 1, .triangle 34 1, .corridorLower 4 5]

-- Original cycle f177afe8b597675233fd7908c6b11859523c37df81f2cc02521c52f213610c8b; original global index 18827.
def localCycle00222 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 6, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, -1, -1, -2, 0, 3, 0, -2, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 0, .gapLower 6 0, .thetaNext 5, .corridorUpper 4 5, .triangle 34 2, .gapLower 6 5, .triangle 27 0, .triangle 15 0, .corridorLower 1 2]

-- Original cycle f3c6220ee036775892337abe467cd79d149724c01f62562a2d7ccb7dd0009f90; original global index 19016.
def localCycle00223 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 33 2, .gapLower 6 4, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f4e19877665c23903025d2fa9e6fa87ed3fea1ef857b94e0606873b70e36aa01; original global index 19090.
def localCycle00224 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, 0, -3, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true] }
  origin := ![.triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 30 1, .gapLower 6 1, .gapUpper 1 5]

-- Original cycle f542610fe57ef15ad08179af166667c3c69fd5801340561a977b2a91ee064a92; original global index 19117.
def localCycle00225 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Original cycle f58275caffb1c64516b6730f85c9e645406695c42775cd0716f52576d62b43c0; original global index 19143.
def localCycle00226 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 6, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 2, .gapLower 6 3, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle f5a74acfa135a61c138614625e15091ab163eaad64c6d6eebd89c382ffd6071b; original global index 19156.
def localCycle00227 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Original cycle f693830174561d8b192f5e09f0c3bb7bd399541ab308f29768613d9881bcc740; original global index 19239.
def localCycle00228 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle f7e6c7f651b1eea35676436d5394f95935ca1e6223e3fad9c59574d3b4b44c0f; original global index 19327.
def localCycle00229 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .gapLower 6 2, .corridorLower 5 6]

-- Original cycle f8bad1c038dcd4f58202a5d47cf4596332a8c2f034403de149cd1903df783d20; original global index 19398.
def localCycle00230 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 6 1, .corridorLower 5 6]

-- Original cycle f99601cde1e56ab02e4f603355494bc2fe3a413ddf29fe8ca5f5c8a8048029dd; original global index 19456.
def localCycle00231 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Original cycle fe3cfe3d478295a381137cb70084d0d476c9244318c39c91f254efd571555be6; original global index 19874.
def localCycle00232 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 6, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 2, 0, -2, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapLower 6 6, .triangle 30 2, .gapLower 6 3, .triangle 11 1, .triangle 10 0, .triangle 20 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle ff6e03fdc9105aa89eef350eef274b706fd4622f19830a0c4e3b1adaac14906d; original global index 19971.
def localCycle00233 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 5, .distance 0 6, .distance 1 6, .distance 5 6, .theta 6, .theta 5]
    constant := ![3, 0, 0, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, true, false, true, false, true] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 2, .triangle 14 2, .gapLower 6 2, .triangle 24 1, .gapLower 6 0, .thetaNext 5]

-- Original cycle ff88416fed5373c33d68430d8b59f8b933fdc1a56976736e611cf86975b5299a; original global index 19981.
def localCycle00234 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 1 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![4, 0, -1, 0, -2, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 4 6, .triangle 25 2, .triangle 16 0, .triangle 18 2, .gapLower 6 2, .gapLower 6 1, .corridorLower 4 6]

def library : Library := fun id => if id < 117 then (if id < 58 then (if id < 29 then (if id < 14 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 10 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))) else (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))))) else (if id < 21 then (if id < 17 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none))) else (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))) else (if id < 25 then (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none))) else (if id < 27 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)))))) else (if id < 43 then (if id < 36 then (if id < 32 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none)))) else (if id < 39 then (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none))) else (if id < 41 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none))))) else (if id < 50 then (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))) else (if id < 54 then (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none))) else (if id < 56 then (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))))))) else (if id < 87 then (if id < 72 then (if id < 65 then (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 63 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)))) else (if id < 68 then (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none))) else (if id < 70 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none))))) else (if id < 79 then (if id < 75 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 77 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none)))) else (if id < 83 then (if id < 81 then (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))) else (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none)))))) else (if id < 102 then (if id < 94 then (if id < 90 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none))) else (if id < 92 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 98 then (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))) else (if id < 100 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id = 99 then some localCycle00099 else none)) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))))) else (if id < 109 then (if id < 105 then (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))) else (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none)))) else (if id < 113 then (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none))) else (if id < 115 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none)) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))))))) else (if id < 176 then (if id < 146 then (if id < 131 then (if id < 124 then (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id = 123 then some localCycle00123 else none)))) else (if id < 127 then (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))) else (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))))) else (if id < 138 then (if id < 134 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none)))) else (if id < 142 then (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none))) else (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)))))) else (if id < 161 then (if id < 153 then (if id < 149 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))) else (if id < 151 then (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none)) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)))) else (if id < 157 then (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none))) else (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))))) else (if id < 168 then (if id < 164 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none))) else (if id < 166 then (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none)) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)))) else (if id < 172 then (if id < 170 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none))) else (if id < 174 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))))))) else (if id < 205 then (if id < 190 then (if id < 183 then (if id < 179 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id = 178 then some localCycle00178 else none))) else (if id < 181 then (if id < 180 then (if id = 179 then some localCycle00179 else none) else (if id = 180 then some localCycle00180 else none)) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)))) else (if id < 186 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))) else (if id < 188 then (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id = 187 then some localCycle00187 else none)) else (if id < 189 then (if id = 188 then some localCycle00188 else none) else (if id = 189 then some localCycle00189 else none))))) else (if id < 197 then (if id < 193 then (if id < 191 then (if id = 190 then some localCycle00190 else none) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none))) else (if id < 195 then (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none)) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none)))) else (if id < 201 then (if id < 199 then (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id = 198 then some localCycle00198 else none)) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none))) else (if id < 203 then (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)))))) else (if id < 220 then (if id < 212 then (if id < 208 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none))) else (if id < 210 then (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)))) else (if id < 216 then (if id < 214 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id = 213 then some localCycle00213 else none)) else (if id < 215 then (if id = 214 then some localCycle00214 else none) else (if id = 215 then some localCycle00215 else none))) else (if id < 218 then (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)) else (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id = 219 then some localCycle00219 else none))))) else (if id < 227 then (if id < 223 then (if id < 221 then (if id = 220 then some localCycle00220 else none) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none))) else (if id < 225 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none)))) else (if id < 231 then (if id < 229 then (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none)) else (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none))) else (if id < 233 then (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 154 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20864)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 5, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 2, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 11 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20865)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 5, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 2, 3, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 181 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20866)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 85 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20867)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 177 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20868)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 194 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20869)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 178 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20870)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 176 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20871)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 150 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20872)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 187 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20873)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 3 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20874)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 76 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20875)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 88 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20876)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 126 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20877)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 6, 3, 0], ![4, 1, 2, 5, 3, 0]], proof := .tail 76 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20878)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 2, 3, 0]], proof := .tail 88 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20879)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 2, 3, 0]], proof := .tail 20 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20880)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 2, 1, 3, 0]], proof := .tail 136 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20881)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 46 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20882)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 214 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20883)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 42 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20884)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 2, 1, 3, 0]], proof := .tail 110 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20885)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 58 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20886)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 154 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20887)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 1, 5, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 2, 1, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 34 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20888)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 1, 5, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 2, 1, 3, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 25 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20889)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 2, 1, 3, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 29 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20890)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 78 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20891)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .low6 (![6, 96, 87, 116, 115, 48, 57, 70, 49, 141, 91, 107, 139, 23, 133, 91, 107, 79, 84, 91, 107, 83, 1, 163, 232, 55, 91, 211]) }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20892)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 105 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20893)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 105 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20894)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .low6 (![151, 15, 206, 201, 4, 48, 108, 9, 35, 101, 26, 107, 90, 234, 18, 100, 138, 138, 73, 28, 107, 157, 174, 107, 83, 212, 17, 211]) }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20895)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 128 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20896)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 54 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20897)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .low6 (![152, 197, 109, 53, 180, 145, 50, 135, 193, 169, 123, 0, 172, 193, 71, 132, 119, 119, 19, 162, 193, 193, 69, 221, 221, 179, 60, 65]) }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20898)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 166 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20899)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 76 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20900)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 166 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20901)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 3, 0], ![4, 1, 2, 5, 3, 0]], proof := .tail 76 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20902)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 225 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20903)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 3, 0], ![4, 2, 1, 5, 3, 0]], proof := .tail 76 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20904)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 1, 3, 0], ![4, 2, 5, 1, 3, 0]], proof := .tail 204 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20905)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 2, 1, 3, 0]], proof := .tail 204 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20906)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 6, 1, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 1, 3, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 209 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20907)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 46 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20908)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 209 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20909)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 2, 1, 3, 0]], proof := .tail 63 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20910)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 58 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20911)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 207 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20912)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 5, 1, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 2, 3, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 184 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20913)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 5, 1, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 2, 3, 1, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 25 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20914)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 5, 1, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 2, 3, 1, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 203 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20915)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 5, 1, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 31 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20916)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 0, 6, 4], ![2, 5, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 22 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20917)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 130 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20918)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 130 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20919)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 99 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20920)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 121 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20921)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 142 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20922)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 81 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20923)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 134 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20924)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 3, 1, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 32 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20925)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 32 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20926)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 32 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20927)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 74 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20928)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 13 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20929)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 6, 5, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 3, 1, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 76 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20930)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 5, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 88 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20931)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 5, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 68 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20932)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 5, 1, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 43 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20933)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 5, 1, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 125 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20934)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 0, 4, 6], ![5, 2, 1, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 37 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20935)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 0, 4, 6], ![5, 2, 1, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 38 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20936)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 0, 6, 4], ![5, 2, 1, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 111 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20937)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 0, 6, 4], ![5, 2, 1, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 62 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20938)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 0, 6, 4], ![5, 2, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 231 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20939)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 156 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20940)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 156 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20941)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 61 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20942)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 147 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20943)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 147 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20944)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 208 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20945)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 220 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20946)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![5, 6, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 67 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20947)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 205 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20948)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 205 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20949)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 52 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20950)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 52 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20951)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![5, 6, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 92 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20952)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 52 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20953)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![5, 6, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 92 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20954)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![6, 5, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 12 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20955)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![6, 5, 3, 1, 0, 4], ![6, 5, 2, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 106 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20956)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![6, 5, 3, 1, 0, 4], ![6, 5, 2, 1, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 127 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20957)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 4, 5, 6], ![1, 2, 0, 3, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 94 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20958)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 4, 5, 6], ![1, 2, 0, 3, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 97 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20959)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 41 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20960)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 114 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20961)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .low6 (![146, 33, 217, 116, 164, 14, 190, 21, 171, 7, 183, 56, 185, 213, 168, 168, 168, 168, 113, 122, 129, 45, 36, 148, 182, 137, 153, 8]) }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20962)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low6 (![75, 189, 120, 116, 164, 14, 190, 40, 233, 215, 80, 210, 104, 95, 39, 223, 30, 198, 161, 183, 195, 117, 89, 218, 182, 137, 153, 8]) }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20963)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 4, 3]], proof := .tail 2 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20964)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 4, 3]], proof := .tail 158 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20965)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 4, 3]], proof := .tail 159 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20966)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 159 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20967)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .low6 (![16, 224, 144, 186, 219, 14, 149, 192, 47, 44, 47, 47, 47, 51, 66, 10, 10, 10, 226, 229, 229, 229, 86, 202, 165, 103, 118, 77]) }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20968)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 4, 3]], proof := .tail 191 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20969)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 0, 3]], proof := .tail 227 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20970)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 0, 3]], proof := .tail 155 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20971)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 173 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20972)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 173 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20973)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 27 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20974)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .low6 (![93, 170, 131, 186, 72, 14, 149, 124, 175, 160, 199, 222, 104, 98, 5, 230, 230, 230, 143, 216, 216, 216, 64, 202, 165, 112, 118, 77]) }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20975)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 4, 3]], proof := .tail 191 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20976)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 0, 3]], proof := .tail 227 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20977)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 0, 3]], proof := .tail 82 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20978)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 0, 3]], proof := .tail 200 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20979)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 173 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20980)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 173 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20981)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 27 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20982)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 173 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20983)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 59 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20984)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 0, 5], ![6, 1, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 140 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20985)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 0, 5], ![6, 1, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 188 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20986)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 4, 5, 6], ![1, 2, 0, 3, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 167 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20987)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 4, 5, 6], ![1, 2, 0, 3, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 196 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20988)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 102 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20989)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 24 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20990)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 228 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20991)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (20864 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 20864 ≤ id.val) (hhigh : id.val < 20992) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 20864)) = true := by
  let j : Fin 128 := ⟨id.val - 20864, by omega⟩
  have hsum : 20864 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (20864 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard163
