import Jsp000404.N4R2RowDataReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0

set_option Elab.async false

namespace Jsp404.N4R2ReplayData.LeafShard171
open N4R2RowDataReplay

-- Original cycle 0090163c9f15f8beb00bfdd0bf34f2c9ab8b7732ef72d59b63bb479e7ef0cf2e; original global index 48.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 07194acc0c9a835df34d695e731bed22e1e992f45a1e7da556242af905c1d118; original global index 586.
def localCycle00001 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 07cd55215fbfd1a430455f162205ea208c4c6a793d24a8c7ff76153d96d5a456; original global index 633.
def localCycle00002 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .theta 2]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 17 0, .triangle 18 0, .corridorLower 2 6]

-- Original cycle 07e06e2be8c7114f2bcde87b0d21cb4f94c3485d43cdc679efcb3cb6edf04de7; original global index 635.
def localCycle00003 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 0a7b4afac831cefce036ff4dc8cc2093bbe98f8fad4896245fcc9febc20d511a; original global index 832.
def localCycle00004 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 0b9e85ff9f602836d11f080724fb7cf4a31cd91ea0cd7315ea9e5b84a203fc1b; original global index 930.
def localCycle00005 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, -1, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 29 0, .corridorLower 4 6, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 0cc263080b79190884abf041023ef3c214f5e80b771d8a248a32afdf9de1f021; original global index 1009.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 27 2, .triangle 29 1, .corridorLower 4 6]

-- Original cycle 104eb232d363a57bb854dda57059adf1fadd3de194ec25faaa2c4e32d7e74fac; original global index 1310.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .corridorLower 1 2]

-- Original cycle 10a250acb41ec2522ed2b3205c82d6c581ab908b392b92af6ba530fee68cfdad; original global index 1335.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 5, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 2, .triangle 22 1, .triangle 19 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 143e2c0ee8a5b33fde8202f152dd414edfad26ae9bf6d4aeb50132db69b5585a; original global index 1597.
def localCycle00009 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 154fd2ca74d1eb0f2cce6e4b1efcf79b174bfb5cd02f7436dd72af73039827cd; original global index 1685.
def localCycle00010 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 24 0, .gapLower 1 2, .corridorLower 1 4]

-- Original cycle 159d518c6c5420460eb8184dce3e40a0f60dd12dc6ee256fd7e314903fdb6b66; original global index 1712.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 2, .triangle 22 1, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 15b22aaac554ceab8ba8cc466544de93335b8f7e741ba29bcd0a5b1a58a71e64; original global index 1724.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 16e3070731b1b4256305c61816b1c9a16f9a87180dbbadb4d3077d89ca0fab1a; original global index 1800.
def localCycle00013 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .gapLower 5 0]

-- Original cycle 1f675583dccbcb48fa91d560b68dacfd6562895f11bc81ff293c761b9e17e96e; original global index 2409.
def localCycle00014 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Original cycle 1f6dd66b433e0481202af9216f8275be919fbcad6abe2eb8607e7b24d6cd3103; original global index 2414.
def localCycle00015 : Cycle where
  length := 18
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 2, 0, -1, 0, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapUpper 1 5, .triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 22035ffd876d19882d4bfbab1e29536b6baa64747ab4c80c21b9cb1afbfafe0d; original global index 2604.
def localCycle00016 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 22a16145ec009adb13cb9f3b6e57a0abf5f21998fc4c2ffdc58a2576539bdc0a; original global index 2651.
def localCycle00017 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 22 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 238b89bdbe8439be15064e0679afa074691c4f1b8ae0e58f0baa121b6412a9a9; original global index 2726.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 24ce130d4d9df92d435c8b1693773e7e7fe6b13c6b05225dfa6a9bc0067b8771; original global index 2823.
def localCycle00019 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 26e9815e083d233f8f3b4ed40d0982e582b7da5b7d8ea11f57e14f3893ea4ce9; original global index 2981.
def localCycle00020 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 28637467332901a7ea00b1a9905212511948d82d8d9313905403919d6beb1a00; original global index 3098.
def localCycle00021 : Cycle where
  length := 17
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 28 1, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 2e05007eeda5be5d12d5c6b6ba81893459a27fb76c4345958df812da2745cba4; original global index 3514.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 2, .triangle 24 0, .triangle 30 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 2eec9e2bfad6717f490baf46058369569f1caa0b3030d98cc0897b175db91462; original global index 3589.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 3120eecef2d447cae13260310581fd9586d5e4383dc7e76ff5b5a443c9693fd7; original global index 3746.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Original cycle 3a8a3df9a91af333b2dbf07ed7f6c671828c683739c7dc85353576b7812a8612; original global index 4519.
def localCycle00025 : Cycle where
  length := 16
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 2, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapUpper 1 5, .triangle 0 2, .triangle 7 0, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 4170751e06e6acc267a195222b0ab7af0ddf35e58dd1a1f82722e8084d43d57a; original global index 5048.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 4259d7d3c21d0935c1fe3a3fef204e405dc419a1e6d5296eecf1f442fa19c1f9; original global index 5111.
def localCycle00027 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2]
    constant := ![0, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true] }
  origin := ![.triangle 16 2, .triangle 22 0, .triangle 34 0, .triangle 30 2, .gapUpper 2 4]

-- Original cycle 438459c8c76b5168ac233069efe306414757b05b55daf4092f47923c0c947ec7; original global index 5216.
def localCycle00028 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 45e4a3f9b38502a900c8b483cdc7206ab167d9e8a41d4b21546ee100f3971be2; original global index 5405.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 23 2, .triangle 24 1, .triangle 30 0, .gapLower 2 2, .gapLower 4 0]

-- Original cycle 46dcf14868f9d8f896cf88f1da0166aa5917bdd40f660be3604ab35a75fb369a; original global index 5493.
def localCycle00030 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle 4cba25c090e62c96433988775f28110883f0e65b2d2d424a022d1e813ffe5deb; original global index 5956.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 51fc48ae9154c9232037039abc7cda102a362a9fb41292a98baf4fe666b54a7a; original global index 6376.
def localCycle00032 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 561ae8ff988bf608b68fbbeb5adcb429e1bff1832d4d16c8fdbeb4d6a3b19ffc; original global index 6676.
def localCycle00033 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 22 0, .triangle 28 0, .triangle 29 0, .corridorLower 4 6, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 56260e77328956e5946d32db8f37448a4600779ff2c76f09d77f710b26063c56; original global index 6680.
def localCycle00034 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, -1, 3, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 5d60b7b4c7069f376c480afbe62ebc8bb4fe7efce655412463cfc22b5227cf53; original global index 7268.
def localCycle00035 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 2, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapUpper 1 5, .triangle 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 5d7200c52e621972f750f772f9f3b2f9acf89fc38d23ab61f444056d0839de78; original global index 7275.
def localCycle00036 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle 5eec70e62d574e7e733c932899598d2e351d7dddd7b112ba5d3de222bdce25ad; original global index 7389.
def localCycle00037 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Original cycle 5f4f2855e3ac879e5dac1e2f7a74180f7cdc128c5e6ff949c27f31e76b6deb15; original global index 7420.
def localCycle00038 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, 0, -1, -1, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, true] }
  origin := ![.triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 24 2, .gapUpper 1 5]

-- Original cycle 61b2b4df2e0a0df218d1598edb5eb31204aad5d11b5f498bcd7ce8b3281fbd6a; original global index 7624.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 0, .triangle 17 0, .corridorLower 1 2]

-- Original cycle 68ceb683ec0766fefdd5589505f89959620d598656555446f44a8d8fb613d0fb; original global index 8151.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .theta 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 0, .triangle 30 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 6b6461a4c74e6eced678dc5859de01b7b5ed75ba036a13e6cb041da1316c4ca3; original global index 8359.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Original cycle 6c1a7d9b914f18685b95147306809781411ac2128ecedf44471458f65f79bc41; original global index 8425.
def localCycle00042 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle 6cb569067f3c4cefe2d03eab1d4fcd16c15c7aa4453ec3c634126e705132b400; original global index 8458.
def localCycle00043 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 34 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 6da300ad7ca59f340b91ad2cd8d4410deaf4b9cfa02cf2b5eb0a52be1f7734d9; original global index 8521.
def localCycle00044 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2]
    constant := ![0, 2, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 15 2, .gapUpper 3 2, .triangle 33 1, .triangle 34 0, .triangle 28 0, .triangle 16 0]

-- Original cycle 7061ff68d0c8ebbbaef7b5058d4745c7c27e7224141bb620e4311d4b8d1c527e; original global index 8705.
def localCycle00045 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 29 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 70feacbcf2a150378df338c3635ea1957d4960f63f7d7bed8ca97a043bc1cae0; original global index 8761.
def localCycle00046 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaUpper 1, .corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 28 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaLower 4]

-- Original cycle 72c7edb07d5f4127abef7dac5868ca165360bc2964400b4912644765242b2821; original global index 8889.
def localCycle00047 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, 0, -1, -1, -1, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 73cd684545fbd93f9137264d3a4e4c402420681cb50cef425d28ff46139e90dc; original global index 8978.
def localCycle00048 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 77ace17e8f112405f0e7f947976728ad69ff4db0e64f5041cdf992af4f746713; original global index 9258.
def localCycle00049 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle 79ac4c5ddb0bb75be491562272db3d3e1a230f6a61c99487a37ef7b690993be1; original global index 9413.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 7a67e722efee9144aeecd37e902d9f9f9b2376469f5c5310dfffb91b995e5dd1; original global index 9471.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle 7b867f07865c334293258c41ffd8870c93e1d0ad6635eda555c431686a554a7a; original global index 9560.
def localCycle00052 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 34 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 7d1fcc7571d1c48ac84ca63a67442a634a3dfd00b2832acac0ed4c875c6fe58e; original global index 9694.
def localCycle00053 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, -1, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 83553ae81827c0532ce78420cabcf2cb9b2126fde5587c8cc93fc1a34aa50a21; original global index 10183.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .gapLower 4 0]

-- Original cycle 866f14a63773d35372f9f0db590a60553b5506fd5c0926a2f1ee8e38621940ab; original global index 10423.
def localCycle00055 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 2, 0, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapUpper 1 5, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 867267ae1d3e360ed5d55b9e577b10c56a5b3773d1303c581a713b36a72c7657; original global index 10425.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle 89719e19e5af164188cc7c144562f16a8b39d6080203aacc0a0976d80f3c4673; original global index 10636.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .distance 2 5, .theta 5]
    constant := ![3, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .triangle 30 0, .gapLower 5 0]

-- Original cycle 89e2aa475052d082b791e90f0ab4ef67e65b733c896cdbc01fd218cb08e0d2e7; original global index 10684.
def localCycle00058 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle 8cd9aa10bde9fedf8835f878964f30278e6c3cded2478251f399b68e002213dd; original global index 10895.
def localCycle00059 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .triangle 28 0, .gapLower 4 0]

-- Original cycle 909d4e34a4504d20e5c505586d4bbe5451d01628fcb62d01b9746cac42d8b6b3; original global index 11193.
def localCycle00060 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .corridorLower 1 3, .thetaLower 1]

-- Original cycle 94d8f474e4ce2869139d12ab5f8b3627c75241285b9071711ee4a9f99f51ed8f; original global index 11555.
def localCycle00061 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 96f043224988bdd4d9917cbd63f0a15db8b7e4bce2231787fd86c96e32aed6c7; original global index 11730.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 2 6, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 2, .triangle 18 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle 97f40a27b03f747a3e25edb4a6c4408f27c12ca481fc38d232230887ee3fc750; original global index 11800.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .gapLower 5 2, .triangle 17 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle 9bed4378815957a70ac9bfec97a027c78800c3a7e5a663dfb28c6f5af656fadc; original global index 12126.
def localCycle00064 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 16 0, .triangle 18 2, .triangle 21 1, .corridorLower 1 3]

-- Original cycle a9001885b8632b4a2bb73eb12d460bc2459395ef48360f2f64187b99cb5d9907; original global index 13156.
def localCycle00065 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle a9736b0634bb544e371a2ccbd70db81bf0350df9f8b5eee7c3733fceef79011d; original global index 13192.
def localCycle00066 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle aa9fe70858b5e1875623836b9a724b8e91d75e01b9b4e5132c3eea411a9320c6; original global index 13293.
def localCycle00067 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle ae45c0f7c17254bf65d67c6fc22ac8cecff9152894b08c206ce1a02b89491d8c; original global index 13599.
def localCycle00068 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Original cycle aea3c0981c07ec4854a82fce302082e054ddbe0f13a97bb02c823de258eaf93b; original global index 13632.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle af22479f0c7d5cd168a7289c9e8697aa0ea3fe84e9a8d3254ad53cb0a3213a6f; original global index 13676.
def localCycle00070 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 0, -1, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 0, .triangle 28 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle b13c8dfded3ada156518acff84207673fe8602972d209af04110e6b3a4cd7eb4; original global index 13844.
def localCycle00071 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 22 2, .triangle 24 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle b51d0d86360b4707cf9571a4c5199fc99b9036477c600ac57dc7bcd912c9b0cd; original global index 14151.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 2, .triangle 12 0, .triangle 22 0, .triangle 23 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle b86cf50707ffb06630c3ca7c7c53fd25109a5995ba2c135bd69351a2d988ce16; original global index 14392.
def localCycle00073 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Original cycle b8cf722c63f199d616c79b8e9c56253ae420c998c02419fcb6dedc72c2f8ce39; original global index 14426.
def localCycle00074 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 22 0, .triangle 16 1, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle bd9b40e6eb92b4fd7525a2c671417cb4a83f546ff633dab3797266b173c52a76; original global index 14789.
def localCycle00075 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 29 0, .gapLower 4 0]

-- Original cycle be1c9c483d212db6a952c32c78cf685f55ea4c4bb4c3f3f073e94989d6f2307c; original global index 14827.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 34 1, .triangle 30 0, .triangle 17 0, .triangle 16 0, .gapLower 4 0]

-- Original cycle be5594ad4689433543ff1a657cd15f272f2eaa43920876ec9fd77978dd634ad0; original global index 14850.
def localCycle00077 : Cycle where
  length := 13
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 7 0, .triangle 17 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle c24ada768b2dc616fa2c5431cf95b2f7ef777c035a4e0f4b34dc23502a24dbc1; original global index 15170.
def localCycle00078 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 0, .triangle 29 0, .triangle 23 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle c2c06f6caaca679f6cc19f4d10bd2c05d72db63b0d9ed42f3eae53924c48a888; original global index 15198.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 2, .triangle 30 0, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle c6964fe823d2002eb4488eebc25748d93b4aae1bef53888e256556d772e9c002; original global index 15488.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .distance 3 6, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .triangle 27 0, .corridorLower 3 6, .thetaNext 2, .thetaNext 1]

-- Original cycle cb9a2e3429d83ecfdec6645a23ee6eeb91578733be9d4a05c0222d9a5bbfd615; original global index 15909.
def localCycle00081 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 22 0, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 29 0, .gapLower 4 0]

-- Original cycle cbd684fc4d05bedc727de828f35486b809f23de8eeeba4eb7ff271fd3334132d; original global index 15929.
def localCycle00082 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 16 2, .triangle 19 1, .triangle 21 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle cc1a96364c7b4f0c456164fa7de21592a719533cdd5e7a875b5e071218daaed2; original global index 15952.
def localCycle00083 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 1 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 22 2, .triangle 24 0, .triangle 30 0, .gapLower 2 2, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle cca7cbfc81a0235fecfe627c703b9521e3b96da6f76496471924c0826a396d9a; original global index 15997.
def localCycle00084 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .corridorLower 1 3]

-- Original cycle cd367e3da0f626756d8d19806688cf8371f44e595856bb2bd3e3f4cd61b5109d; original global index 16037.
def localCycle00085 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Original cycle ce884f9e7e891830b6003c539e8470f37d13ae3dddb8f5150911db13665354cb; original global index 16129.
def localCycle00086 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 28 0, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Original cycle d0ceeba7fe1d8f8a378efe8ab6c613f9e06f317577c0c112879f69c9c258899d; original global index 16300.
def localCycle00087 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1]

-- Original cycle d61e96468c7f86c09681a5176648d0d3fabfd1c4deff48489778967e8afb2437; original global index 16715.
def localCycle00088 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 6, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 7 0, .triangle 17 0, .triangle 16 2, .triangle 23 0, .triangle 29 2, .triangle 30 1, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .corridorLower 1 3]

-- Original cycle d82718e88e583a90c30d622ab36576e9251471e4ecdd11402f395c830d0afc5d; original global index 16873.
def localCycle00089 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5]

-- Original cycle d9eeda8e61844c720c0b696d76c3e9c129ff3514d2f878b43a500c495377f29d; original global index 17027.
def localCycle00090 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 0, .triangle 30 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle dc68bb7836c209bd0831fca2dc61fb246ecc489886632da21cc74f838f72abf1; original global index 17225.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 6 1, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Original cycle ddf181aaf306fe6889787eb7e1d0bd1a6ee29f29d8e7888b95baaa356da45631; original global index 17350.
def localCycle00092 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 5, .distance 5 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 2, .triangle 14 0, .triangle 34 0, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle dfc768afd8801a34c99ddac28ab7a19414f1849acb453043b6cf3b31a03e3c8f; original global index 17481.
def localCycle00093 : Cycle where
  length := 13
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, 0, 2, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 13 0, .triangle 23 2, .gapUpper 1 5, .triangle 0 2, .triangle 7 0, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .gapLower 4 0]

-- Original cycle e32273edb5fc5dd0299515389c50c5b78b05c00ada2b846be1217958492beee2; original global index 17765.
def localCycle00094 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 28 0, .triangle 34 0, .triangle 24 2, .gapUpper 1 5]

-- Original cycle ead2c895865061a82149ee77ff110919c47f2d27ebd564790ed6647182eaa934; original global index 18343.
def localCycle00095 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Original cycle f38526b23cab5ef65fca13cfa71f5cbbd01c2f7d3a4d5edc3506b7a30e0a0227; original global index 18999.
def localCycle00096 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 12 0, .triangle 28 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaNext 1]

-- Original cycle f8e951c4d14c825385d3fd27924f994ed17de5c0bf922f863ef4b8410d97b3b4; original global index 19412.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 4, .distance 4 5, .distance 2 5, .distance 1 2, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 2, .triangle 12 0, .triangle 28 2, .triangle 17 0, .triangle 16 0, .triangle 29 0, .corridorLower 4 6]

-- Original cycle fb5e8ef2c347e076e07d2358392a931199ba95236c294e13fd93809fa4dfebf8; original global index 19617.
def localCycle00098 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 5, .distance 2 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 0, .triangle 28 1, .triangle 29 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

-- Original cycle fc36a8ccf95950f47661c50fd0b4d54ceff40e68cbfa49e84a3ac60eb853bd45; original global index 19698.
def localCycle00099 : Cycle where
  length := 12
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, -1, -1, -1, 3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3]

-- Original cycle fe37914f4acbba412276fb3113f420d43dcca75639d641bca8daee8a73a32c7d; original global index 19869.
def localCycle00100 : Cycle where
  length := 12
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .theta 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, -1, 0, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 17 0, .triangle 30 0, .corridorLower 5 6, .thetaNext 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .corridorLower 2 3, .thetaNext 1]

def library : Library := fun id => if id < 50 then (if id < 25 then (if id < 12 then (if id < 6 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)))) else (if id < 9 then (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none))))) else (if id < 18 then (if id < 15 then (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))) else (if id < 21 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none))) else (if id < 23 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)) else (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id = 24 then some localCycle00024 else none)))))) else (if id < 37 then (if id < 31 then (if id < 28 then (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none))) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none)))) else (if id < 34 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none))) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))) else (if id < 43 then (if id < 40 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none))) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)))) else (if id < 46 then (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))) else (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))))))) else (if id < 75 then (if id < 62 then (if id < 56 then (if id < 53 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id < 52 then (if id = 51 then some localCycle00051 else none) else (if id = 52 then some localCycle00052 else none))) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none)))) else (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id = 61 then some localCycle00061 else none))))) else (if id < 68 then (if id < 65 then (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none))) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)))) else (if id < 71 then (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)))))) else (if id < 88 then (if id < 81 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id = 80 then some localCycle00080 else none)))) else (if id < 84 then (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none))) else (if id < 86 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none)) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none))))) else (if id < 94 then (if id < 91 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))) else (if id < 97 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none))) else (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none)))))))

def namedLeaf000 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 1, 6, 5, 0, 3], ![6, 2, 1, 4, 0, 3], ![5, 2, 1, 4, 0, 3]], proof := .tail 40 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21888)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 5, 0, 3], ![2, 6, 1, 4, 0, 3], ![2, 5, 4, 1, 0, 3]], proof := .tail 45 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21889)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 6, 1, 5, 0, 3], ![6, 2, 1, 4, 0, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 45 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21890)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 6, 4, 5, 1, 0], ![2, 1, 0, 6, 5, 4], ![6, 2, 1, 5, 0, 3], ![6, 2, 1, 4, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 72 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21891)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 6, 0, 3], ![2, 1, 4, 5, 0, 3]], proof := .tail 48 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21892)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 6, 0, 3], ![2, 1, 4, 5, 0, 3]], proof := .tail 68 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21893)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 1, 6, 0, 3], ![2, 4, 1, 5, 0, 3]], proof := .tail 92 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21894)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 1, 6, 0, 3], ![2, 4, 1, 5, 0, 3]], proof := .tail 87 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21895)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 1, 6, 0, 3], ![4, 2, 1, 5, 0, 3]], proof := .tail 31 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21896)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 6, 1, 0, 3], ![2, 4, 5, 1, 0, 3]], proof := .tail 71 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21897)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 6, 5, 1, 0, 3], ![2, 6, 4, 1, 0, 3], ![2, 5, 4, 1, 0, 3]], proof := .tail 27 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21898)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 4, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 0, 6, 5, 4], ![2, 6, 5, 1, 0, 3], ![6, 2, 4, 1, 0, 3], ![5, 2, 4, 1, 0, 3]], proof := .tail 4 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21899)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 4, 2, 0], ![3, 6, 4, 5, 1, 0], ![2, 1, 0, 6, 5, 4], ![6, 2, 5, 1, 0, 3], ![6, 2, 4, 1, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 33 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21900)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 0, 6, 5, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 6, 1, 0, 3], ![2, 4, 5, 1, 0, 3]], proof := .tail 28 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21901)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 1, 0, 3]], proof := .tail 0 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21902)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 4, 2, 0], ![3, 6, 5, 4, 1, 0], ![2, 1, 0, 6, 5, 4], ![5, 6, 2, 1, 0, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 1, 0, 3]], proof := .tail 51 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21903)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![3, 6, 5, 4, 2, 1], ![3, 6, 5, 4, 2, 0], ![3, 6, 5, 4, 1, 0], ![2, 1, 0, 6, 5, 4], ![6, 5, 2, 1, 0, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 1, 0, 3]], proof := .tail 46 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21904)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 42 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21905)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 42 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21906)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 15 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21907)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 42 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21908)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 21 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21909)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 30 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21910)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 5, 0], ![2, 1, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 9 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21911)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 4, 5, 0], ![2, 6, 1, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 12 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21912)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 4, 5, 0], ![6, 2, 1, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 24 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21913)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![1, 2, 6, 0, 3, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 19 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21914)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![1, 6, 2, 0, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 25 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21915)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 95 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21916)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 61 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21917)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 88 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21918)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 5, 0], ![2, 1, 6, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 77 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21919)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 82 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21920)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 2, 5, 0], ![3, 6, 4, 1, 5, 0], ![2, 6, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 82 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21921)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 2, 5, 0], ![6, 3, 4, 1, 5, 0], ![6, 2, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 1, 2, 0, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 2 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21922)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![2, 1, 6, 0, 3, 4], ![1, 2, 5, 4, 3, 0]], proof := .tail 13 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21923)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![2, 1, 6, 0, 3, 4], ![2, 1, 5, 4, 3, 0]], proof := .tail 60 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21924)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 1, 4, 3, 0]], proof := .tail 26 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21925)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 6, 0, 4, 5], ![2, 1, 6, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 1, 4, 3, 0]], proof := .tail 90 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21926)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 4, 1, 3, 0]], proof := .tail 52 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21927)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 6, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 4, 1, 3, 0]], proof := .tail 11 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21928)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 6, 4, 5, 1, 0], ![2, 1, 6, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 4, 2, 1, 3, 0]], proof := .tail 70 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21929)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![2, 6, 1, 0, 3, 4], ![2, 5, 4, 3, 1, 0]], proof := .tail 57 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21930)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 6, 1, 0, 4, 5], ![2, 6, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 2, 4, 3, 1, 0]], proof := .tail 90 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21931)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 5, 2, 0], ![3, 6, 4, 5, 1, 0], ![2, 6, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 4, 2, 3, 1, 0]], proof := .tail 70 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21932)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 5, 2, 0], ![6, 3, 4, 5, 1, 0], ![6, 2, 1, 0, 4, 5], ![6, 2, 1, 0, 3, 5], ![6, 2, 1, 0, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 80 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21933)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 2, 6, 0, 4, 3], ![1, 2, 5, 4, 3, 0]], proof := .tail 41 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21934)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![1, 6, 2, 0, 4, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 41 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21935)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![1, 6, 2, 0, 4, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 18 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21936)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 6, 0, 5, 4], ![1, 2, 6, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 41 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21937)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 0, 5, 4], ![1, 6, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 18 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21938)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 3 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21939)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 5, 0], ![2, 1, 6, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 91 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21940)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 2, 4, 5, 0], ![3, 6, 1, 4, 5, 0], ![2, 6, 1, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 6 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21941)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 4, 5, 0], ![6, 2, 1, 0, 5, 4], ![6, 1, 2, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 86 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21942)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![1, 2, 6, 0, 4, 3], ![1, 2, 5, 4, 3, 0]], proof := .tail 76 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21943)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![1, 6, 2, 0, 4, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 93 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21944)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 20 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21945)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 2, 1, 4, 3, 0]], proof := .tail 75 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21946)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 16 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21947)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 5, 0], ![2, 1, 6, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 5 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21948)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 82 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21949)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 2, 5, 0], ![3, 6, 4, 1, 5, 0], ![2, 6, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 82 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21950)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 2, 5, 0], ![6, 3, 4, 1, 5, 0], ![6, 2, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 1, 2, 0, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 2 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21951)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![2, 1, 6, 0, 4, 3], ![1, 2, 5, 4, 3, 0]], proof := .tail 54 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21952)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![2, 1, 6, 0, 4, 3], ![2, 1, 5, 4, 3, 0]], proof := .tail 75 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21953)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![2, 6, 1, 0, 4, 3], ![2, 5, 1, 4, 3, 0]], proof := .tail 29 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21954)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 0, 5, 3], ![6, 2, 1, 0, 4, 3], ![5, 2, 1, 4, 3, 0]], proof := .tail 75 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21955)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![2, 6, 1, 0, 4, 3], ![2, 5, 4, 1, 3, 0]], proof := .tail 75 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21956)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 2, 1, 0, 4, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 75 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21957)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 6, 4, 5, 1, 0], ![2, 1, 6, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 2, 1, 0, 4, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 98 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21958)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![2, 6, 1, 0, 4, 3], ![2, 5, 4, 3, 1, 0]], proof := .tail 75 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21959)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 6, 1, 0, 5, 4], ![2, 6, 1, 0, 5, 3], ![6, 2, 1, 0, 4, 3], ![5, 2, 4, 3, 1, 0]], proof := .tail 81 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21960)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 5, 2, 0], ![3, 6, 4, 5, 1, 0], ![2, 6, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 2, 1, 0, 4, 3], ![5, 4, 2, 3, 1, 0]], proof := .tail 8 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21961)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 3, 4, 5, 2, 1], ![6, 3, 4, 5, 2, 0], ![6, 3, 4, 5, 1, 0], ![6, 2, 1, 0, 5, 4], ![6, 2, 1, 0, 5, 3], ![6, 2, 1, 0, 4, 3], ![5, 4, 3, 2, 1, 0]], proof := .tail 36 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21962)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 6, 0, 5, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 6, 0, 3], ![1, 2, 4, 5, 3, 0]], proof := .tail 44 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21963)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 6, 0, 5, 4], ![1, 2, 6, 5, 0, 3], ![1, 2, 6, 4, 0, 3], ![1, 2, 5, 4, 3, 0]], proof := .tail 7 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21964)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 6, 0, 5, 4], ![1, 2, 6, 5, 0, 3], ![1, 6, 2, 4, 0, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 67 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21965)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 0, 5, 4], ![1, 6, 2, 5, 0, 3], ![1, 6, 2, 4, 0, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 38 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21966)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 6, 0, 5, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 6, 0, 3], ![1, 2, 4, 5, 3, 0]], proof := .tail 58 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21967)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 6, 0, 5, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 85 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21968)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 6, 2, 0, 3], ![1, 4, 5, 2, 3, 0]], proof := .tail 79 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21969)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![1, 6, 5, 2, 0, 3], ![1, 6, 4, 2, 0, 3], ![1, 5, 4, 2, 3, 0]], proof := .tail 94 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21970)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 4, 6, 5, 0], ![2, 1, 6, 0, 5, 4], ![1, 2, 6, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 67 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21971)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 0, 5, 4], ![1, 6, 2, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 78 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21972)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 4, 6, 5, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![1, 6, 5, 2, 0, 3], ![6, 1, 4, 2, 0, 3], ![5, 1, 4, 2, 3, 0]], proof := .tail 74 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21973)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 4, 5, 0], ![2, 1, 6, 0, 5, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 62 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21974)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 6, 4, 5, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 53 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21975)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 6, 0, 5, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 6, 0, 3], ![1, 2, 4, 5, 3, 0]], proof := .tail 37 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21976)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 34 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21977)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 6, 2, 0, 3], ![1, 4, 5, 2, 3, 0]], proof := .tail 35 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21978)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 6, 0, 3], ![4, 1, 2, 5, 3, 0]], proof := .tail 14 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21979)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 6, 2, 0, 3], ![4, 1, 5, 2, 3, 0]], proof := .tail 66 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21980)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 1, 2, 3, 0]], proof := .tail 47 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21981)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 2, 0, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 1, 2, 3, 0]], proof := .tail 17 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21982)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 4, 5, 0], ![2, 1, 6, 0, 5, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 64 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21983)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 2, 4, 5, 0], ![3, 6, 1, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 84 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21984)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 6, 1, 2, 0, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 49 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21985)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 4, 0], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 2, 0, 3], ![6, 4, 1, 2, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 23 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21986)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 1, 6, 0, 5, 4], ![5, 1, 2, 6, 0, 3], ![4, 2, 1, 6, 0, 3], ![1, 2, 4, 5, 3, 0]], proof := .tail 73 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21987)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 1, 6, 2, 0, 3], ![4, 2, 1, 6, 0, 3], ![1, 4, 2, 5, 3, 0]], proof := .tail 55 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21988)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 6, 0, 3], ![4, 1, 2, 5, 3, 0]], proof := .tail 56 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21989)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 6, 0, 3], ![4, 2, 1, 5, 3, 0]], proof := .tail 69 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21990)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 5, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 6, 1, 0, 3], ![4, 2, 5, 1, 3, 0]], proof := .tail 22 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21991)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 4, 0], ![2, 1, 6, 0, 5, 4], ![5, 6, 1, 2, 0, 3], ![4, 6, 2, 1, 0, 3], ![4, 5, 2, 1, 3, 0]], proof := .tail 99 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21992)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 4, 0], ![2, 1, 6, 0, 5, 4], ![6, 5, 1, 2, 0, 3], ![6, 4, 2, 1, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 65 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21993)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 5, 6, 0, 3], ![1, 2, 4, 6, 0, 3], ![1, 2, 4, 5, 3, 0]], proof := .tail 63 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21994)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 5, 0, 3], ![1, 2, 6, 4, 0, 3], ![1, 2, 5, 4, 3, 0]], proof := .tail 39 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21995)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 5, 0, 3], ![1, 6, 2, 4, 0, 3], ![1, 5, 2, 4, 3, 0]], proof := .tail 96 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21996)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 2, 6, 5, 0], ![3, 4, 1, 6, 5, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 1, 2, 4, 3, 0]], proof := .tail 1 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21997)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 6, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 2, 1, 4, 3, 0]], proof := .tail 50 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21998)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 4, 2, 5, 0], ![3, 4, 6, 1, 5, 0], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 45 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 21999)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 4, 2, 5, 0], ![3, 6, 4, 1, 5, 0], ![2, 1, 6, 0, 5, 4], ![6, 2, 1, 5, 0, 3], ![6, 1, 2, 4, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 97 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22000)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 6, 0, 3], ![1, 2, 4, 5, 3, 0]], proof := .tail 14 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22001)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 5, 0, 3], ![2, 1, 6, 4, 0, 3], ![1, 2, 5, 4, 3, 0]], proof := .tail 43 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22002)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 6, 0, 5, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 6, 0, 3], ![1, 2, 4, 5, 3, 0]], proof := .tail 59 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22003)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 1, 6, 0, 5, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 6, 0, 3], ![1, 2, 4, 5, 3, 0]], proof := .tail 89 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22004)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 6, 0, 3], ![2, 1, 4, 5, 3, 0]], proof := .tail 14 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22005)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 5, 0, 3], ![2, 1, 6, 4, 0, 3], ![2, 1, 5, 4, 3, 0]], proof := .tail 10 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22006)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 5, 0, 3], ![2, 6, 1, 4, 0, 3], ![2, 5, 1, 4, 3, 0]], proof := .tail 83 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22007)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 4, 6, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 1, 6, 5, 0, 3], ![6, 2, 1, 4, 0, 3], ![5, 2, 1, 4, 3, 0]], proof := .tail 100 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22008)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 5, 0, 3], ![2, 6, 1, 4, 0, 3], ![2, 5, 4, 1, 3, 0]], proof := .tail 45 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22009)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 4, 6, 5, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 6, 1, 5, 0, 3], ![6, 2, 1, 4, 0, 3], ![5, 2, 4, 1, 3, 0]], proof := .tail 45 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22010)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 6, 4, 5, 2, 0], ![3, 6, 4, 5, 1, 0], ![2, 1, 6, 0, 5, 4], ![6, 2, 1, 5, 0, 3], ![6, 2, 1, 4, 0, 3], ![5, 4, 2, 1, 3, 0]], proof := .tail 72 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22011)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 6, 0, 3], ![2, 1, 4, 5, 3, 0]], proof := .tail 59 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22012)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 6, 0, 3], ![2, 1, 4, 5, 3, 0]], proof := .tail 58 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22013)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 1, 6, 0, 3], ![2, 4, 1, 5, 3, 0]], proof := .tail 14 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22014)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 3, 5, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 6, 0, 5, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 1, 6, 0, 3], ![2, 4, 1, 5, 3, 0]], proof := .tail 32 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22015)) namedLeaf127 = true :=
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
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (21888 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 21888 ≤ id.val) (hhigh : id.val < 22016) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 21888)) = true := by
  let j : Fin 128 := ⟨id.val - 21888, by omega⟩
  have hsum : 21888 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (21888 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct

end Jsp404.N4R2ReplayData.LeafShard171
