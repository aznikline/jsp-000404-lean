import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard073
open N4R2RowDataReplay

-- Original cycle 012f1a055fc6b8c830f06ea9d549edff13746b4c2279e1d057023b944336c73e; original global index 105.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 2, .triangle 24 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 05bb2f17575ebc9da3163b70c08470629a91983de74b1da0eedee10b37157594; original global index 475.
def localCycle00001 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 0d416fb9e40b934e7c72b5cb47ba11c9c3b565588780d98165be4508668396b7; original global index 1049.
def localCycle00002 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 32 2, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 13d5afa5c7cc97950558c92fd92b649f1a41191677efea764a9b73c1cfb1aaef; original global index 1572.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 13fb4ba237bf89dc7ac12781bf90cf3dbc71a38ea40c85882f4ceedb7b81d600; original global index 1576.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 1800a592f3da3d028c18aea9f25e3502d72a91cd041469b374acc8a756424155; original global index 1875.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 1bf45a8097652880a4e97ab635cd3044c713c7ab7c2c6acf9e36c3988d385a77; original global index 2159.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 1cb0856ab02cccb1ecf016132602e778a230525100350b5fbaff663b92de49e8; original global index 2208.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 0, .triangle 26 0, .triangle 33 2, .gapLower 3 0]

-- Original cycle 1f237d6f46e6d16ad4e7feec5bc96b472dfee76308cd63d3214864b88277b58b; original global index 2392.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 2 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 27 2, .triangle 29 1, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 2544f949de3921d0236ba9d3c4d07de87b902d388245e9c294783ffce14e6852; original global index 2865.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 29415a2f98f0244484d0ec9c998e2140c32504e09191162f50bf2a29a81c8173; original global index 3148.
def localCycle00010 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .corridorLower 5 6]

-- Original cycle 2bfb09e1c00e90e02e4da16ce7901b08bc163d366dad89fafbeaeb4fcdc5922b; original global index 3364.
def localCycle00011 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 0, .triangle 27 0, .gapLower 3 0]

-- Original cycle 2c129a8c72fb065b212cac41f2bd466553730fd8dc49087e5a1ff683f48c6d57; original global index 3372.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 2c65fd55d572f3992ddcd530a2296a7199886a2fe2b7ad88e4de3eee371bda35; original global index 3394.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Original cycle 2cdcca57ad4e9feb4bd11e93f588390dc4aec889d1d0fcdbb0033b2a47605494; original global index 3427.
def localCycle00014 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 2f4af45835a8cf61a340d599629993a5c20cb86d9134fdae4fa0807b392d2a0e; original global index 3617.
def localCycle00015 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle 30543f376d3abc590445b9e08030912d32e43663f3c1f3a596cba5f684c1b87d; original global index 3680.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 3098f28af78457888a3cc1b3b40322cbcf9dbae01a57323810db1750ce585eae; original global index 3707.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Original cycle 3457e39216c3e225094ea2f1701405d9590cf7c40830f292cf5774aff4d0cc81; original global index 4014.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 1 2, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2, 2, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, true, false] }
  origin := ![.triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 29 2, .gapUpper 2 4, .gapUpper 2 5, .triangle 0 0]

-- Original cycle 3692cec34133167cc73064de6f2060e2002aed99f190b23683636ad05781ffd8; original global index 4191.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle 36e81e76a629027079145aad056bb226bf98e6f9a1b4175dd610dc2cda2edc04; original global index 4217.
def localCycle00020 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 385e71c8a2fe45b94db6ffc0dee60ffa5d856fc29f72f587d1d29d03bb630314; original global index 4332.
def localCycle00021 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 2 4, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 29 0, .corridorLower 2 4]

-- Original cycle 3ac3f043a83f44552d28298adf604ba3620685c6ba263fe3a32c249538763a96; original global index 4538.
def localCycle00022 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, false] }
  origin := ![.triangle 2 2, .gapUpper 4 4, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0]

-- Original cycle 3f8c8eaf17859c48543f762d8c56820bf0bca8565f3bf1cb70ad25d063e3c9b1; original global index 4911.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .distance 3 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 0, .triangle 27 0, .triangle 33 1, .corridorLower 3 5]

-- Original cycle 41f6c3226ecc7a9236c5582668432499c90459bd50879597821d92a332362244; original global index 5083.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 47ec77b62bff821a9ef94a4c36f8e04354e3718763ab66e651db432b37bed29c; original global index 5567.
def localCycle00025 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 5 2, .triangle 11 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4979672604816768bf411855b186e64d920b3299b8688155c522d2e283766790; original global index 5694.
def localCycle00026 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 8 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 4aaca6a55f65083dcced7d6d0c4fc4dbdf63916a3be58a8445e96bbe8daa3867; original global index 5792.
def localCycle00027 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 4d64fd25347173d3c47d61786f01c40d4cc37797bead3ea9b267b56f35476051; original global index 6009.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .corridorLower 3 5]

-- Original cycle 52446932c711798105803143db6f7d234abc64a62d20e15cdfe2d30c8280d6cf; original global index 6396.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 27 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle 63d34376bf670c783516cecd401ea5cc0aa672146dd49951f55625a294b8cb84; original global index 7779.
def localCycle00030 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 66f51b768f2b4e3256f0e66c2f3939acf74fb3be46b88fa63b8fa086af982a25; original global index 7997.
def localCycle00031 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3]

-- Original cycle 66f5fa868816ee9730b03c65eac04c5a02e5b9b6d393b68ff13122c9d152f001; original global index 7998.
def localCycle00032 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 2, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Original cycle 693dcb83c95eadd6080c4c990fb12bfc7d2c690a03c6d7a0b4fab3ea3687f6ef; original global index 8185.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle 6ad74cf58431b3a00312c4fe52f1a740fc24ba86a1eed4996e41fa78c43319f9; original global index 8317.
def localCycle00034 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .distance 3 5, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 0, .triangle 26 0, .triangle 33 2, .corridorLower 3 6]

-- Original cycle 6d76559fc63e9838256c67265b876c6991aef49656c4d73469cfb34e1ca0bfbc; original global index 8508.
def localCycle00035 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 717bf4d48de7070d481356211bfd1bcfd839e1568c1eab778f29e49ed3172f62; original global index 8806.
def localCycle00036 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 785b3ecbaf0c67dcd11c991b5023fabe2e217351eb954a52ad4ac2d664c0eb57; original global index 9304.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle 7de0a828e66a631324f6bcc3a7183f6c297a492256454407ce74799177dbebb4; original global index 9777.
def localCycle00038 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 2, .distance 2 3, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 2, .triangle 5 0, .triangle 27 0, .triangle 33 1, .corridorLower 5 6]

-- Original cycle 7ef99ae81dc30adca651aae1f52d7e3748a02226b5dc5ac69d8579e8dc3c4de0; original global index 9856.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .gapLower 3 0]

-- Original cycle 7ff5b8ea7b9115637f2856ecfe2095674cd2d43f5d84e8fa15560074179930a2; original global index 9928.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle 81641e61aa4935f440070413dd74a51a6a5ad2aaccbd8c1c4c8ddffb5e027a59; original global index 10052.
def localCycle00041 : Cycle where
  length := 7
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 8354badda56662252901d3e5780002b67b858d8ce22bc22c3d8ad6e28b36ac60; original global index 10182.
def localCycle00042 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 8d518626202a7627d9bddc05724a547c73a210fd662ad7d70ef42b5563be3c57; original global index 10927.
def localCycle00043 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 8da656bc034f972ebc28f4dbd8c237719dd8cf3e59d35b734a5f098f86ab11ef; original global index 10956.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 8f51b8aabc70148827750c18be7a02054905414c9b970b96a8735944c84aaf85; original global index 11091.
def localCycle00045 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4]

-- Original cycle 90a019f6902777aa12b0a0f354b323f0e2291ab06a971368b09bb11fd6cd616b; original global index 11196.
def localCycle00046 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 4 0, .triangle 23 1, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle 9806a2c9b1be75e63b161cd99e46d46760a1ad3ed231b41b6a4084b237c03130; original global index 11809.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .distance 0 2]
    constant := ![-1, -1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true] }
  origin := ![.triangle 5 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapUpper 5 1, .triangle 7 1]

-- Original cycle 98d44df256630fffb2764d2998b87ff27ed3a9e37b1e30f7c961e9196822fe59; original global index 11867.
def localCycle00048 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle 9c15973df029739db90f969d3f09d7043c183c24321f8ed4de4c59faa78ce58d; original global index 12142.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 31 2, .triangle 33 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle 9fc3b1d3ca68fed76c12c2427e659f05aea5dbe231604746812fbd5b47777e0a; original global index 12435.
def localCycle00050 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle a0b2dadc09c6105b60012bfaf52462220979493d477fc63a4c2174aafa6af12d; original global index 12500.
def localCycle00051 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle a2d4b967f498efd7f20070f49d039381feebb0b2021de810e62305f2b8d3f438; original global index 12667.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle a39caca02541b5b4360165cb1600cbf59f7e66b722e9b61a946c325b15f27659; original global index 12716.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 1 3, .distance 3 6, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 21 0, .triangle 27 2, .triangle 8 0, .triangle 0 1, .triangle 2 0, .triangle 19 1, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle a5e084328bef45c0b2e41b8d78c3d06588cc1d95b2d5b5803f2a0f45b56ad543; original global index 12886.
def localCycle00054 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle aea2e3d275df6786cf8341f0bf0e36969d40377eab031e62ab4c0496ad895c86; original global index 13631.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, 0, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .gapLower 5 4, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 29 0, .triangle 32 0, .corridorLower 3 4]

-- Original cycle b041d041e87be487ee99746fbaf88249268872d48c2deefdb027e6b842f2f0b4; original global index 13761.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .corridorLower 3 5]

-- Original cycle b494ee37bc5b3db2834c2b2ae246e6ba910584bcab758488328a4b639445b4aa; original global index 14102.
def localCycle00057 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 2, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Original cycle b9c6b13615b265c7c06559d8dc85dda41edc9ae40370dfd85fc88c42215c2f43; original global index 14502.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .gapLower 3 0]

-- Original cycle bdd1d638f197932c34ff7a6509ac2db4a3a79059094f34cb2c5332a90988616e; original global index 14804.
def localCycle00059 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle bdf46b60dc65cec001989b35633c4c986baecf6314e1e06ac47fefd9dcb5d1de; original global index 14814.
def localCycle00060 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

-- Original cycle bf2ac02fb47871ae91ea8070e13a10bd7be80f08f2096dad88e31d0cdeb9c17d; original global index 14916.
def localCycle00061 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 6, .distance 2 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 0, .triangle 0 0, .triangle 4 0, .triangle 18 1, .triangle 27 1, .triangle 33 1, .corridorLower 5 6]

-- Original cycle c010058485e8214d7885a23bb443620f15f447e6d7f01f031ec2433e3268afe1; original global index 14992.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 34 0, .triangle 33 0, .gapLower 3 2, .triangle 25 0, .corridorLower 2 3]

-- Original cycle c5f44d299861fa9aca0a293452094b9547ac8e2205321e491b68dc24203a6d0a; original global index 15437.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .theta 2]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .triangle 34 0, .triangle 30 0, .gapLower 2 2, .corridorLower 2 4]

-- Original cycle c8aff41020c5f95f8b959af9c58c795f24a8f1b2137fc40e02a790c24c98a830; original global index 15675.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle cb5f7238964a2e3fab7997942e7b3112ab020d5418062d5355c5cf92220af977; original global index 15888.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .corridorLower 3 5]

-- Original cycle cbc0a73a8804aa5bbbdddbde1d7f86605c06b9cc059bd9c407bc85b667558a47; original global index 15921.
def localCycle00066 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle db45120d293142984acad1d1998e2261264e6f072b6c7be0cb756f71087eae6c; original global index 17138.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .triangle 32 0, .gapLower 4 1, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle dc7fae586dcc2bfbd54cea6697a07cc3a11af25e85e8bb2877fc0261ae686bdc; original global index 17231.
def localCycle00068 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 6, .distance 1 2, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 4, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 2, .triangle 18 0, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 25 2, .triangle 28 0, .corridorLower 4 5, .thetaLower 4]

-- Original cycle de31e3ade105234f091f6395c20583d764002c760190a795a3d7b81ed901a1e3; original global index 17374.
def localCycle00069 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 19 1, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 0, .thetaNext 2]

-- Original cycle de507853ea02158bcb00fcaef7f730bcb911a03d0519c977c6a04f9ee1961b5d; original global index 17379.
def localCycle00070 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, 0, 2, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 2, .gapUpper 4 4, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e0035918fb6115169aac7c4ab056a58d48d01e40b1b70c34be739e43dc0bc775; original global index 17511.
def localCycle00071 : Cycle where
  length := 17
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 2 4, .theta 2, .distance 1 2, .distance 2 6, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 2 4, .corridorUpper 1 2, .triangle 18 0, .triangle 30 1, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e0c3fbe6ababd51378c827405fccadc538480a7291af7a13e7836f26a89a7d4a; original global index 17574.
def localCycle00072 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 7 0, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaLower 3]

-- Original cycle e2d9b6ee59c3a691fd5cdea5dc4050dac53d29c49318285933273ec36b00721e; original global index 17743.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 0, .triangle 23 0, .triangle 34 1, .triangle 31 0, .triangle 25 0, .corridorLower 2 3]

-- Original cycle e58b9e87a6d1eac78791fe5c626d5eb0175972dd29c258e2d074177ea5bdc832; original global index 17956.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .triangle 28 0, .triangle 29 2, .gapLower 2 1, .gapLower 3 0]

-- Original cycle e9d86599a9947a5c11355bf9cf06f2c2d69e79d048ebe369ca4bbef7d46aeaa9; original global index 18270.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 3, .distance 3 4, .theta 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 1 2, .triangle 17 0, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 5 0, .triangle 25 0, .corridorLower 3 4, .thetaNext 2]

-- Original cycle ebb7c3503a042101cf07dd47dddd67b610aea53388963ca3fe1aad5f537b2906; original global index 18395.
def localCycle00076 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 0 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1]
    constant := ![0, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false] }
  origin := ![.triangle 2 2, .gapUpper 4 4, .triangle 32 2, .triangle 21 0, .triangle 1 0]

-- Original cycle ed5cf76c1538cf2befaccc10144f02ea280417fd3bfe31d3684b7bd51026ef5b; original global index 18528.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 28 0, .gapLower 2 2, .triangle 27 0, .gapLower 3 0]

-- Original cycle f06eb7ff35d712c11756422afc8fdab6b75c3a76091ce2a1317f4be75a0c0569; original global index 18748.
def localCycle00078 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 4, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle f10051569e4c859c16942f8fbd793d8648f231818ee26109354262987e100dfb; original global index 18796.
def localCycle00079 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3]

-- Original cycle f166a47f3263948282764533fd7b2e73228a30166fe6828f12ab4d5c0a6749c8; original global index 18820.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 31 0, .triangle 32 0, .gapLower 4 1, .gapLower 2 1, .gapLower 3 0]

-- Original cycle f236e593344007378c7ad6bc35cae3344f2e74d2dde582bb502846a1d8c3bf4a; original global index 18890.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 1 2, .distance 2 6, .distance 0 2, .distance 0 1, .distance 1 4, .distance 3 4, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 18 0, .triangle 8 0, .triangle 0 1, .triangle 2 0, .triangle 19 1, .triangle 25 0, .corridorLower 2 3]

-- Original cycle f2d1a4255445946b9fcb875033f04b4d2f103811e6af3ae4f0e23b04633e9950; original global index 18927.
def localCycle00082 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4]

-- Original cycle f30bfe12bd288e55b7c0f46f7d04863f9b1650836e36b6a4a923d1be435b39cd; original global index 18947.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 5, .distance 3 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 2, .triangle 12 0, .triangle 31 0, .triangle 25 0, .triangle 27 0, .corridorLower 3 6]

-- Original cycle f43a85820aa2857c2bd59fed6b70eb88eabcbde3919b92bbe377e3ce72099d3c; original global index 19043.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 1 2, .distance 0 1, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 1 2, .triangle 0 0, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3]

-- Original cycle f5bf101670fc032e164737ebf6826d028cd45c79f522af3df0e05e5e9f0015ed; original global index 19171.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 22 0, .triangle 28 0, .triangle 29 2, .gapLower 2 1, .gapLower 3 0]

-- Original cycle f80f5e720d15b28cfbab3e1ccf2f2ef1b893edf9666b69f642d305141f5dd20e; original global index 19340.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 0, .triangle 28 0, .gapLower 2 2, .triangle 27 0, .gapLower 3 0]

-- Original cycle fa201abef1c641474c153b269e5665768879b4b3cab97727eb33b6e5381719bc; original global index 19502.
def localCycle00087 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 0 1, .distance 1 4, .distance 2 4, .distance 3 4, .theta 3, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 17 0, .triangle 0 0, .triangle 2 0, .triangle 16 1, .triangle 25 1, .corridorLower 3 4, .thetaLower 3]

-- Original cycle fe986331a1c3b0b8e245d56cc9ce3d3ab35b2bbdf6197d28623e3313f3851ccc; original global index 19903.
def localCycle00088 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 1, .gapLower 3 0]

-- Original cycle fedf40118ffa89621502fe112f46c0e44364d09f8ee418789f73cd66537ae504; original global index 19929.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 4, .distance 2 3, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 1 3, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 25 0, .triangle 26 0, .corridorLower 3 5]

def library : Library := fun id => if id < 45 then (if id < 22 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 16 then (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id = 15 then some localCycle00015 else none)))) else (if id < 19 then (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none))) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))))) else (if id < 33 then (if id < 27 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none)))) else (if id < 30 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none))) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))))) else (if id < 39 then (if id < 36 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id = 35 then some localCycle00035 else none))) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)))) else (if id < 42 then (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))))) else (if id < 67 then (if id < 56 then (if id < 50 then (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)))) else (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))))) else (if id < 61 then (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)))) else (if id < 64 then (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))))) else (if id < 78 then (if id < 72 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id = 71 then some localCycle00071 else none)))) else (if id < 75 then (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))))) else (if id < 84 then (if id < 81 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none))) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))) else (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 5, 6, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 1, 6, 5, 0], ![2, 3, 1, 6, 4, 0], ![2, 3, 1, 5, 4, 0]], proof := .tail 42 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9344)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 1, 6, 5, 0], ![2, 3, 6, 1, 4, 0], ![2, 3, 5, 1, 4, 0]], proof := .tail 14 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9345)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 1, 6, 5, 0], ![2, 6, 3, 1, 4, 0], ![2, 5, 3, 1, 4, 0]], proof := .tail 43 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9346)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![4, 6, 5, 0, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 1, 6, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 2, 3, 1, 4, 0]], proof := .tail 9 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9347)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 6, 1, 5, 0], ![2, 3, 6, 1, 4, 0], ![2, 3, 5, 4, 1, 0]], proof := .tail 18 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9348)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 1, 5, 0], ![2, 6, 3, 1, 4, 0], ![2, 5, 3, 4, 1, 0]], proof := .tail 18 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9349)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 1, 5, 0], ![2, 6, 3, 1, 4, 0], ![2, 5, 4, 3, 1, 0]], proof := .tail 18 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9350)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 1, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 2, 3, 4, 1, 0]], proof := .tail 35 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9351)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 1, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 2, 4, 3, 1, 0]], proof := .tail 35 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9352)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![6, 2, 3, 1, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 17 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9353)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 4, 5, 0, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 1, 5, 0], ![6, 2, 3, 1, 4, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 83 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9354)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 4, 5, 0, 1, 6], ![2, 3, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 27 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9355)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9356)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 41 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9357)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 1, 6], ![2, 3, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 41 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9358)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 0, 6, 1], ![2, 3, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 41 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9359)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 41 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9360)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 1, 0, 6], ![2, 3, 4, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 46 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9361)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 1, 6, 0], ![2, 3, 4, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 64 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9362)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 6, 1, 0], ![2, 3, 4, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 73 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9363)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 1, 6, 0], ![2, 3, 4, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 24 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9364)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 6, 1, 0], ![2, 3, 4, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 66 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9365)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 5, 6, 1, 0], ![2, 3, 4, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 3 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9366)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 5, 6, 0, 1], ![2, 3, 6, 5, 1, 0], ![2, 3, 6, 4, 1, 0], ![2, 3, 5, 4, 1, 0]], proof := .tail 62 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9367)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 5, 1, 0], ![2, 6, 3, 4, 1, 0], ![2, 5, 3, 4, 1, 0]], proof := .tail 48 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9368)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 5, 1, 0], ![2, 6, 3, 4, 1, 0], ![2, 5, 4, 3, 1, 0]], proof := .tail 80 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9369)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 4, 6, 5, 0, 1], ![2, 3, 6, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 2, 3, 4, 1, 0]], proof := .tail 41 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9370)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![2, 6, 3, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 2, 4, 3, 1, 0]], proof := .tail 67 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9371)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 4, 5, 0, 1], ![6, 2, 3, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 85 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9372)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 4, 5, 0, 1], ![6, 2, 3, 5, 1, 0], ![6, 2, 3, 4, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 77 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9373)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 2, 6], ![3, 4, 5, 0, 1, 6], ![2, 5, 4, 0, 1, 6], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 30 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9374)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 6, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 4, 0, 1, 6], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9375)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 6, 3, 2], ![3, 4, 5, 0, 6, 1], ![2, 5, 4, 0, 6, 1], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 44 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9376)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 3, 6, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 0, 1, 6], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 44 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9377)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 44 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9378)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 44 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9379)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 5 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9380)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 1, 6, 0], ![2, 4, 3, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 84 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9381)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 6, 1, 0], ![2, 4, 3, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 4 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9382)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![2, 5, 6, 3, 1, 0], ![2, 4, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 20 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9383)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 1, 6, 0], ![2, 4, 3, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 54 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9384)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 6, 1, 0], ![2, 4, 3, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 4 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9385)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![2, 5, 6, 3, 1, 0], ![2, 4, 3, 1, 6, 0], ![2, 4, 3, 1, 5, 0]], proof := .tail 6 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9386)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![2, 5, 3, 6, 1, 0], ![2, 4, 3, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 12 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9387)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![2, 5, 6, 3, 1, 0], ![2, 4, 3, 6, 1, 0], ![2, 4, 3, 5, 1, 0]], proof := .tail 12 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9388)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 4, 0, 1], ![2, 5, 6, 3, 1, 0], ![2, 4, 6, 3, 1, 0], ![2, 4, 5, 3, 1, 0]], proof := .tail 49 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9389)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 5, 6, 0, 1], ![2, 6, 5, 4, 0, 1], ![2, 6, 5, 3, 1, 0], ![2, 6, 4, 3, 1, 0], ![2, 5, 4, 3, 1, 0]], proof := .tail 63 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9390)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 4, 6, 5, 0, 1], ![2, 6, 5, 4, 0, 1], ![2, 6, 5, 3, 1, 0], ![6, 2, 4, 3, 1, 0], ![5, 2, 4, 3, 1, 0]], proof := .tail 44 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9391)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 6, 4, 5, 0, 1], ![2, 6, 5, 4, 0, 1], ![6, 2, 5, 3, 1, 0], ![6, 2, 4, 3, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 74 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9392)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 3, 4, 5, 0, 1], ![6, 2, 5, 4, 0, 1], ![6, 2, 5, 3, 1, 0], ![6, 2, 4, 3, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 86 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9393)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 2, 6], ![3, 5, 4, 0, 1, 6], ![2, 5, 4, 0, 1, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 68 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9394)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 6, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 4, 0, 1, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 81 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9395)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 6, 3, 2], ![3, 5, 4, 0, 6, 1], ![2, 5, 4, 0, 6, 1], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 53 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9396)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 3, 6, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 0, 1, 6], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 15 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9397)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 6, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 0, 6, 1], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 37 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9398)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 37 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9399)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 8 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9400)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 39 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9401)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 6, 1, 0], ![4, 2, 3, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 51 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9402)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 2, 6, 3, 1, 0], ![4, 2, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 79 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9403)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 57 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9404)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 58 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9405)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 6, 1, 0], ![4, 2, 3, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 51 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9406)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 2, 6, 3, 1, 0], ![4, 2, 3, 1, 6, 0], ![2, 4, 3, 1, 5, 0]], proof := .tail 58 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9407)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 31 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9408)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 4, 6, 0, 1], ![5, 2, 3, 6, 1, 0], ![4, 2, 3, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 12 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9409)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 2, 6, 3, 1, 0], ![4, 2, 3, 6, 1, 0], ![2, 4, 3, 5, 1, 0]], proof := .tail 12 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9410)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 5, 4, 6, 0, 1], ![2, 6, 5, 4, 0, 1], ![5, 2, 6, 3, 1, 0], ![4, 2, 6, 3, 1, 0], ![2, 4, 5, 3, 1, 0]], proof := .tail 88 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9411)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 5, 6, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 2, 3, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 12 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9412)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 5, 6, 4, 0, 1], ![2, 6, 5, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 2, 6, 3, 1, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 88 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9413)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 6, 2, 3, 1, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 16 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9414)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![3, 6, 5, 4, 0, 1], ![2, 6, 5, 4, 0, 1], ![6, 5, 2, 3, 1, 0], ![6, 4, 2, 3, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 32 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9415)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 6, 2, 3, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 11 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9416)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 3, 5, 4, 0, 1], ![6, 2, 5, 4, 0, 1], ![6, 5, 2, 3, 1, 0], ![6, 4, 2, 3, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 13 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9417)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 2, 6], ![5, 3, 4, 0, 1, 6], ![5, 2, 4, 0, 1, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 50 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9418)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 3, 6, 2], ![5, 3, 4, 0, 6, 1], ![5, 2, 4, 0, 1, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 50 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9419)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 4, 1, 3, 2, 6], ![5, 4, 0, 6, 3, 2], ![5, 3, 4, 0, 6, 1], ![5, 2, 4, 0, 6, 1], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![0, 2, 3, 1, 4, 5]], proof := .tail 60 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9420)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 3, 6, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 0, 1, 6], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 0, 1, 3, 4, 5]], proof := .tail 50 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9421)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![5, 4, 1, 3, 6, 2], ![5, 4, 0, 6, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 0, 6, 1], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 0, 3, 1, 4, 5]], proof := .tail 60 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9422)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 4, 1, 6, 3, 2], ![5, 4, 0, 6, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 3, 0, 1, 4, 5]], proof := .tail 60 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9423)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 4, 6, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 1, 0, 6], ![4, 3, 2, 1, 0, 6], ![2, 3, 1, 0, 4, 5]], proof := .tail 89 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9424)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 1, 6, 0], ![4, 3, 2, 1, 0, 6], ![2, 3, 1, 4, 0, 5]], proof := .tail 59 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9425)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 6, 1, 0], ![4, 3, 2, 1, 0, 6], ![2, 3, 4, 1, 0, 5]], proof := .tail 56 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9426)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 2, 6, 3, 1, 0], ![4, 3, 2, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 65 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9427)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 60 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9428)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 4, 6, 0, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 1, 6, 0], ![4, 3, 2, 1, 6, 0], ![2, 3, 1, 4, 5, 0]], proof := .tail 33 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9429)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 6, 1, 0], ![4, 3, 2, 1, 6, 0], ![2, 3, 4, 1, 5, 0]], proof := .tail 56 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9430)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 2, 6, 3, 1, 0], ![4, 3, 2, 1, 6, 0], ![2, 4, 3, 1, 5, 0]], proof := .tail 65 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9431)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 60 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9432)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 4, 6, 0, 1], ![5, 2, 3, 6, 1, 0], ![4, 3, 2, 6, 1, 0], ![2, 3, 4, 5, 1, 0]], proof := .tail 28 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9433)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 3, 4, 6, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 2, 6, 3, 1, 0], ![4, 3, 2, 6, 1, 0], ![2, 4, 3, 5, 1, 0]], proof := .tail 28 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9434)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 3, 6, 4, 0, 1], ![5, 2, 6, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 19 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9435)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![5, 6, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 23 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9436)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![5, 6, 4, 0, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 23 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9437)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![5, 6, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 23 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9438)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 3, 4, 0, 1], ![5, 6, 2, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 69 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9439)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 4, 0, 1], ![5, 6, 2, 3, 1, 0], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 7 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9440)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 5, 4, 1, 3, 2], ![6, 5, 4, 0, 3, 2], ![6, 5, 3, 4, 0, 1], ![6, 5, 2, 4, 0, 1], ![6, 5, 2, 3, 1, 0], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 34 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9441)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 2, 5, 6], ![4, 3, 0, 1, 5, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 1, 0, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 52 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9442)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 2, 5, 6], ![4, 3, 0, 1, 5, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 1, 0, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 87 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9443)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 2, 5, 6], ![4, 3, 0, 1, 5, 6], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 82 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9444)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 2, 5, 6], ![4, 3, 0, 1, 6, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 78 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9445)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 2, 6, 5], ![4, 3, 0, 1, 6, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .tail 22 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9446)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 6, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 26 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9447)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 6, 3, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 0, 6, 1, 5], ![3, 2, 1, 0, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 2, 3, 1, 4]], proof := .tail 29 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9448)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![4, 1, 3, 2, 6, 5], ![4, 0, 3, 2, 6, 5], ![4, 3, 0, 1, 6, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .tail 22 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9449)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![4, 1, 3, 2, 6, 5], ![4, 0, 3, 6, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 1, 3, 4]], proof := .tail 26 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9450)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![4, 1, 3, 2, 6, 5], ![4, 0, 6, 3, 2, 5], ![4, 3, 0, 6, 1, 5], ![4, 2, 0, 6, 1, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 2, 3, 1, 4]], proof := .tail 29 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9451)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![4, 1, 3, 6, 2, 5], ![4, 0, 3, 6, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 1, 3, 4]], proof := .tail 76 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9452)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![4, 1, 3, 6, 2, 5], ![4, 0, 6, 3, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 0, 6, 1, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 0, 3, 1, 4]], proof := .tail 29 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9453)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![4, 1, 6, 3, 2, 5], ![4, 0, 6, 3, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 6, 0, 1, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 0, 1, 4]], proof := .tail 25 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9454)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![4, 1, 6, 3, 2, 5], ![4, 0, 6, 3, 2, 5], ![4, 6, 3, 0, 1, 5], ![4, 6, 2, 0, 1, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 0, 1, 4]], proof := .tail 38 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9455)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![4, 6, 1, 3, 2, 5], ![4, 6, 0, 3, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 6, 0, 1, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 1, 0, 4]], proof := .tail 1 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9456)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 4, 1, 3, 2, 5], ![4, 6, 0, 3, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 6, 0, 1, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 1, 4, 0]], proof := .tail 2 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9457)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 4, 1, 3, 2, 5], ![6, 4, 0, 3, 2, 5], ![4, 3, 6, 0, 1, 5], ![4, 2, 6, 0, 1, 5], ![3, 2, 6, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 2, 3, 4, 1, 0]], proof := .tail 21 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9458)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![4, 6, 1, 3, 2, 5], ![4, 6, 0, 3, 2, 5], ![4, 6, 3, 0, 1, 5], ![4, 6, 2, 0, 1, 5], ![3, 2, 1, 0, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 1, 0, 4]], proof := .tail 61 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9459)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 4, 1, 3, 2, 5], ![4, 6, 0, 3, 2, 5], ![4, 6, 3, 0, 1, 5], ![4, 6, 2, 0, 1, 5], ![3, 2, 1, 6, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 1, 4, 0]], proof := .tail 10 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9460)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 4, 1, 3, 2, 5], ![6, 4, 0, 3, 2, 5], ![4, 6, 3, 0, 1, 5], ![4, 6, 2, 0, 1, 5], ![3, 2, 6, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 2, 4, 1, 0]], proof := .tail 21 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9461)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 4, 1, 3, 2, 5], ![6, 4, 0, 3, 2, 5], ![6, 4, 3, 0, 1, 5], ![4, 6, 2, 0, 1, 5], ![3, 6, 2, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 55 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9462)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 4, 1, 3, 2, 5], ![6, 4, 0, 3, 2, 5], ![6, 4, 3, 0, 1, 5], ![6, 4, 2, 0, 1, 5], ![6, 3, 2, 1, 0, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 47 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9463)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 5, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 1, 0, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 36 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9464)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 5, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 1, 5, 6], ![3, 2, 1, 0, 5, 6], ![0, 2, 1, 3, 4, 6], ![0, 2, 1, 3, 4, 5]], proof := .tail 40 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9465)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 5, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 0, 1, 5, 6], ![3, 2, 1, 0, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 70 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9466)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 5, 2, 6], ![4, 3, 0, 5, 1, 6], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 72 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9467)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 5, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 1, 5, 6], ![3, 2, 1, 0, 6, 5], ![0, 2, 1, 3, 6, 4], ![0, 2, 1, 3, 5, 4]], proof := .tail 71 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9468)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 5, 6, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 2, 1, 6, 3, 4], ![0, 2, 1, 5, 3, 4]], proof := .tail 45 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9469)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 6, 5, 2], ![4, 3, 0, 5, 6, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 2, 6, 1, 3, 4], ![0, 2, 5, 1, 3, 4]], proof := .tail 0 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9470)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![4, 1, 3, 2, 5, 6], ![4, 0, 3, 6, 5, 2], ![4, 3, 0, 6, 5, 1], ![4, 2, 0, 1, 6, 5], ![3, 2, 1, 0, 6, 5], ![0, 6, 2, 1, 3, 4], ![0, 5, 2, 1, 3, 4]], proof := .tail 75 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 9471)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (9344 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 9344 ≤ id.val) (hhigh : id.val < 9472) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 9344)) = true := by
  let j : Fin 128 := ⟨id.val - 9344, by omega⟩
  have hsum : 9344 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (9344 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard073
