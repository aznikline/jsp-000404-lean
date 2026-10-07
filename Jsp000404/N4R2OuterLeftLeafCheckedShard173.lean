import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard173
open N4R2OuterLeftReplay

-- Cycle fingerprint 0051a070384576f00c66125c32b5f32affc870d2df7e45d5c4e43e6a147d9cc7.
def localCycle00000 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3]
    constant := ![0, -2, -2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 21 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1]

-- Cycle fingerprint 040010c843f1e72d07622410e97acb10c763dc847b85f9d0df76970f72ba321b.
def localCycle00001 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, 0, -2, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 04b71f9b247eb2daed088509e53e310db3d1fe8bad3ad9f8e67eacec671ee5f3.
def localCycle00002 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 04c6ac4ce88e5bf753c433214bfc48990b9c50aeccb00176c79e7cec83a5390d.
def localCycle00003 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 060a8a9383de5adcee44721d93401527bff2e3cfdeaf0d430201156fc2490db2.
def localCycle00004 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5]
    constant := ![-1, 0, 0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, false, false, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 15 0, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint 07347e86c1bffa5eb1b2cd0fc7c8286b2fb523880a090abb8ee9dede8060782f.
def localCycle00005 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![0, 2, -2, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true, true] }
  origin := ![.thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 19 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 07de91727e323ca9ee79a7d9b741083b6cc9305302c9abfb437bd72d47eac606.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .gapLower 1 2, .triangle 16 1, .gapLower 4 0]

-- Cycle fingerprint 098283bdb3a291b41344460a4c4b62681032d0b87b8769e7ce2914e4c3802e9e.
def localCycle00007 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 0b32ced5dab8c99729a7136dd404b352b14b57e7b7813b6824cffb2dd9cf60cf.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 0bd0876f451a22a64b382b27a895c65518869402e39406285c8480f3726d8f1b.
def localCycle00009 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 2, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 0f2972c4b2eb5dd30ec50d8c7ccb64f40790fa2a83eae3ba29511d118dca3fb4.
def localCycle00010 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 0f755c488b9b52a2a2724075d1b5be06a36166525769c741a10384cbbf7d0576.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 4 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .triangle 28 0, .gapLower 2 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 1247dca2911679c52bcbe796a20837bef1a7f8e9316687746c9e147dc2772d8d.
def localCycle00012 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint 13008f22700ff4e11f19a99908ca98303c30890ff8a82c9c87a7d5a6d44a329b.
def localCycle00013 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint 13dd7f78252a53215b67a6fe538a36a88b5543faf3eb59a1c9cdab5bd21c2695.
def localCycle00014 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, 0, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, true, true, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 21 2, .triangle 24 1, .gapLower 1 1]

-- Cycle fingerprint 13eaee517f82b6c2b1cf42bba5a6263300d5a0ab479406c5023e0e06d316714e.
def localCycle00015 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4]
    constant := ![3, -1, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 20 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 149de33b6771c5f22a29e58c5f46b350aa54b14aa8a8905aa6bf82971bc8f2a2.
def localCycle00016 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 23 0, .triangle 22 0, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint 15772f8ad3675ab2a4622e4216bd3a15b5494462e71e34ec107e644e8ec9b442.
def localCycle00017 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 25 1, .triangle 26 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 161a486e59576b89a4999875ad79616f1794d1cf769654ecfa1e26093a0b7469.
def localCycle00018 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 1671daf3bffc6eb638988bc5287a094b2ca1caafecbe9ea4ee1e39d9c5fef712.
def localCycle00019 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 6, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .corridorUpper 0 1, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint 1b0979728d34a1accb75f689121c2bf388823f3357eef1543784465b666d28d1.
def localCycle00020 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 25 1, .triangle 15 0, .gapLower 1 0, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint 1b9506cdfd297338f92569f12a190d9b604f4c33f1541db35199561b5a9daef8.
def localCycle00021 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6]
    constant := ![0, -2, -2, 3, 0, -1, 0, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, true, true, true] }
  origin := ![.triangle 24 1, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 21 2]

-- Cycle fingerprint 1e77d5e775f278173c66e47cd4b44104021394154a384cec268dc00593360179.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .gapLower 2 2, .triangle 26 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 1ed729964179ff5a4e680241b4dd2c019dcc4727c88e0f8810d57b1e7c4019af.
def localCycle00023 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-2, 0, 0, 3, -1, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 24 1, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint 23d98c6e16f6a253cb153757371c5da7d5d0eba36b8dbefaa283693031ff48e0.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, 0, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 20 2, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 25f8199755a7f749c5583627089ec6f1792cf75986c2b102e862274a0541489a.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 19 1, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 2a0cb091b6439f4c9b32a4fdbeb7de014e9a643dec6abcdf99efe289a6d608f5.
def localCycle00026 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint 2acb90070edb8b9960e59e808af694fd315f6b811149cbc9a1f896b0d64903d1.
def localCycle00027 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 32 1, .gapUpper 4 2]

-- Cycle fingerprint 2c0eb3f0084e0259082c37bb06686050a8cb277901874e5ee11f60a43c515497.
def localCycle00028 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, true] }
  origin := ![.thetaNext 2, .corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .gapLower 1 3, .triangle 21 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2fe9ef377b40c3861bbc85ac8336a267f9f823c95b0daca4997a720c75fc14f1.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 307ed66fb3119f3fcb326ad69eb373c6ad645b12851d927c0634541d21392f73.
def localCycle00030 : Cycle where
  length := 15
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 3145bac4a4da9f06c39c281872cf2ec95aa8896bc9cf97b68579d0f05e39cd62.
def localCycle00031 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 3212106df51a045667c03ab9ded10be0715567478ae459252ad45053e6bbfbb2.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 37289361ee2f086f9209898e490860abb10a5dfa9dd98bd449bd9861f8068e5f.
def localCycle00033 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 38167058942c07b5786a7fd46e0acadaf374bbc42dcd4d1ef2251cf6aca6cee8.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 3, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 27 1, .corridorLower 2 3]

-- Cycle fingerprint 38484819ca130e2177661882ae8241c3f08aea92899d8ce3b45451b6ad34f54a.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint 387ad890bcc1e2441cc48e6bde0f5c70f40497df531cee9f9b6dac8e88088c99.
def localCycle00036 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 18 2]

-- Cycle fingerprint 38c5af3c3f4daeec4fb97a32ed86cc85cb38dd826c2f0ff8561e6be5f8b6412d.
def localCycle00037 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .triangle 0 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 3958f63d58e792604d59eb85683f22f37b74981f02499452201a6d257ba62c63.
def localCycle00038 : Cycle where
  length := 5
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 32 1, .gapUpper 4 2, .triangle 19 1, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 3b69dde2df20273e01d1b86ccd3c754a71a4eec6d5007d085e0ce818dc62db70.
def localCycle00039 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, 0, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 3e4f2dbbd2b41b0878d76d6ca23d63c2a42b3896db399b5e52439564bcaf2a7c.
def localCycle00040 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 0 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 3ef06578ef6a05eefe5e8d31e958b16e8526dadb3d525f3a7373baeb9057be74.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 0, -1, 0, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .corridorUpper 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 3]

-- Cycle fingerprint 3f0c6820273ba9b193717c15ba38efaeb3262e2183a540df832f53da96d22d01.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 40c9773cb1e484abb907e84ee1cae5e8d6dbc0d2786be519baf63e463e869fef.
def localCycle00043 : Cycle where
  length := 4
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5]
    constant := ![-1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, false] }
  origin := ![.triangle 22 0, .gapLower 1 1, .gapUpper 3 2, .gapLower 5 3]

-- Cycle fingerprint 40f91ce0777cfbb144690fc41bf05fdac1b118d46a9c8a94e3ff66f5bdc72304.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -1, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 20 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 412e9b6453c86cdbacaf640656710bdcc754d1b34b2bd8c9a756b7e13cc13ab1.
def localCycle00045 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 5]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 5, .gapLower 1 6, .triangle 0 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 4229a1f996d6bdd3bb0aac43090dd88808ce5f23bc4ad2081f0139b4d6f06522.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4233e556b54eeeb887a46db2f6a829de2573b80589afbd9d726bf2d2b23ec530.
def localCycle00047 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -1, 0, -1, 3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 44375e4f4f104d8e6069ee562b8660ddfa30a1cdddbe8d00289e5987f7e5f5c8.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 45d12e8ba081429343bf8663e120a53f68fd94d89d97b4f8c335dc6032a01fee.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .triangle 23 1, .triangle 29 0, .triangle 25 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 46dddbde8b52fb8ee1882fbd9afd1c39b4306a51c342e50930187278ccca86c7.
def localCycle00050 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4a2cf3b0c7f8db797e1bea92fbc1aaef271d9463f0d23dee75b097670d04bc39.
def localCycle00051 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 2, .triangle 18 0, .triangle 16 0, .triangle 25 1, .triangle 26 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint 4ac9f288fe21d82ed2707daf60d6da0feb89479872ad804878346bba708631a6.
def localCycle00052 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![0, -1, -1, 0, 3, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, true, false] }
  origin := ![.gapLower 1 2, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint 4b194d633a09f77f7fb5ba76809cb60e529e518c48f82236f3a504a2bf5b5930.
def localCycle00053 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint 4bc1717b7c2930117fb3652546a379487d941a336556d2ae70d0077661231d99.
def localCycle00054 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3]
    constant := ![-1, 0, -1, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 20 0, .gapLower 1 0, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 9 1]

-- Cycle fingerprint 50b90157b62bdcbc15162b656e0dd8fc01ec4f92437b1396a479eb297f55b520.
def localCycle00055 : Cycle where
  length := 14
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6]
    constant := ![-1, -1, -1, 3, -1, -1, 0, -1, -1, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0]

-- Cycle fingerprint 519539146e6fd0083fa734a84df20cb32ac824c4e4d4a524360e855495af9b76.
def localCycle00056 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 16 2, .gapLower 1 4, .corridorLower 1 6, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint 51b14c48b48dbb846984c5a31ed77dbad6e80a6fad99d7bc728785777f61b82d.
def localCycle00057 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 533e50495f74530cc82e3fe4f507f9f0ae5b2f17d52517d6d64937b9c9998e02.
def localCycle00058 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 19 1, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 53d1a234f24503c796debc11a44ea8734b71a632083a26345a32e7782dad54d4.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 29 0, .triangle 16 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 553b959b59ab51619be603ae5c8dc880dc154f765a1cec6caa3eb105a701420d.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3]
    constant := ![0, -1, 3, 0, -1, 0, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 33 1, .triangle 20 0]

-- Cycle fingerprint 5621b00f80b1bac06c58c89feebeec0e643a8e9cbdd92786d6566563b03ec9d9.
def localCycle00061 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .triangle 30 0, .gapLower 2 3, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 576e3d02c40199c1819f9fa29a22e438df4e2862542bc987afc0982983c06af6.
def localCycle00062 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .distance 3 4, .distance 0 3, .distance 3 6]
    constant := ![0, -2, 0, -2, 0, 0, 4, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 21 2, .gapLower 1 3, .triangle 22 1, .gapLower 1 1, .triangle 15 1, .gapLower 3 0, .gapLower 3 6, .triangle 9 0, .triangle 11 0]

-- Cycle fingerprint 5a28d79874061aa88c97bb8cfb69957fd192b0ba3bcd40830a8ac0da13553ac0.
def localCycle00063 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 5f6bf37f160a2a1e37fe37f58d10aa15cd070b7609679a8691d467772e0d209d.
def localCycle00064 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 4, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 60ed0a28dfd5f7b51223593e5e57f084be7b52b5d8fc26b620dca594620c118f.
def localCycle00065 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 1 5, .distance 3 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 1, .gapLower 1 2, .triangle 20 1]

-- Cycle fingerprint 61015886d06e268802691ad23ee2ce4e998baab530dca73686a3411cbd0237d9.
def localCycle00066 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint 66b3bb19ec76d7fb6d9c86ccc110e3afd4b6ca60bf79b0886a44ef73df2311d3.
def localCycle00067 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![-1, -1, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, true] }
  origin := ![.triangle 6 0, .triangle 28 0, .triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2]

-- Cycle fingerprint 694d1c0f5d9dc1bce33397af02ed586a492513102c7c9817456deedaad3a1adf.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, true] }
  origin := ![.triangle 19 1, .triangle 20 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 16 2]

-- Cycle fingerprint 6b8531233834d7dfcdb3d53bf076b9c55776f29472a48aaf13fd0f3e68c218a0.
def localCycle00069 : Cycle where
  length := 17
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, -1, -1, -1, -1, -1, 0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, true, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 6ddb1aec40902caae77dc35d95256998f8432b03df495440c16a41065f217902.
def localCycle00070 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 2, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 6e49c793b596c3d9602357a2e08a87aefee8d74345d370b7095237a4611eda11.
def localCycle00071 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 6e8219c8efd93e23199b3c1103bf732823fc6bfe25d353f4cffed952cd920813.
def localCycle00072 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 718edcc0ac864cbb1b79a0371b6de5e02aefff6badb8c86b779a3345e110180d.
def localCycle00073 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 2]

-- Cycle fingerprint 720cf8e9f28236febdaa1614c2607ad67ce428ef2776db9fcf0ef086fd03f4ce.
def localCycle00074 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 6, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .gapLower 1 3, .corridorLower 1 6]

-- Cycle fingerprint 765c954676868baa39e24e338348f3a82792ab49859130b550fcac94c26dab93.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 2 5]
    constant := ![-1, -1, -1, 0, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, true, true] }
  origin := ![.triangle 30 0, .triangle 33 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 26 2]

-- Cycle fingerprint 77fee745638657f799bdc04fe724b4f2bda31c5f2223724236b74d2b42fc3e59.
def localCycle00076 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 3 5, .theta 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 25 1, .triangle 27 0, .triangle 33 1, .corridorLower 3 5, .thetaNext 2, .thetaNext 1]

-- Cycle fingerprint 79b92192c6d0c7a8d6b962a347c549c754916b442d0668a5b7d2860a541433ab.
def localCycle00077 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 16 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint 7b34010d047c2bb886d8f792b1b59859558ff7e2d594bbfa42349ca3f3ed214d.
def localCycle00078 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 3, .gapLower 1 1, .gapUpper 2 1]

-- Cycle fingerprint 7dfc966d368fd21ebcc1b4dee06aae33ba23961bac4136193816e917a751d671.
def localCycle00079 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 8108f7c52d1a3917405abff544a9f73d36dc179b5b8100ad632d2e0518ffb01b.
def localCycle00080 : Cycle where
  length := 16
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4]
    constant := ![-1, -1, 0, 0, -1, -1, -1, 0, 3, 0, -1, -1, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4]

-- Cycle fingerprint 81ccbcb94da265ff6dec1924401258baafae80b4e40c8f2fffcd7bcef53bbaae.
def localCycle00081 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 8473dd8ed1f92c0ba4afbddd87fba99b911fe342912cf92358209cb4247a7f12.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 5, .triangle 19 1, .triangle 20 0, .corridorLower 3 5, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1]

-- Cycle fingerprint 8558652c00cd5a349a4196d04e21b17a0bf26deea0c755c41a89f882f644f877.
def localCycle00083 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 18 2]

-- Cycle fingerprint 86dbcdc0ff9b56626f1b876b202e5381914eca117220625f219088aefb8e279d.
def localCycle00084 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .triangle 28 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 88fe137fecfa1c3ee6602305e34d3aa615770462b62b34cff3eaea371e9622d3.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3]
    constant := ![-1, 0, -1, -1, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 20 0, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 9 1]

-- Cycle fingerprint 8c70b5836af269605968e99fe0b4b76f500b27efc035838b14c05f3a7f13c1b3.
def localCycle00086 : Cycle where
  length := 5
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 17 0, .corridorLower 2 5]

-- Cycle fingerprint 8ee73f4cebf71e3555a59f9c6109344e7724b642629160b4250001c79d1d5ec2.
def localCycle00087 : Cycle where
  length := 13
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 3, -1, -1, 0, -1, -1, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false, true] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 34 1]

-- Cycle fingerprint 93123188b388334f76dd4531e8c16b8989cffc8f041630bc75e0034a0cfa468b.
def localCycle00088 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 4, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 16 0, .triangle 25 1, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 978eed4b124b6ee28645b6f296d3c51de1e53d4160cf86fa9687eb0d3adac39f.
def localCycle00089 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![3, -2, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .triangle 19 1, .triangle 20 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 98887a5c70278cc221b59c8468f6d65abb997d04c586fd5332c2c645cf9b2b6c.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 99758f12f285c51fb8760c480caba74511acaf08b6c754f8db46ab51c05ff9bf.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .theta 1, .zero, .theta 4]
    constant := ![3, -1, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 1 3, .corridorLower 1 5, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 9a358aedfb5ee9953ceaeb17e5656b9413cf1b5c500bf39a724d2aabef179090.
def localCycle00092 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 1 2, .distance 2 5, .theta 2, .distance 0 2]
    constant := ![-1, 0, -1, -1, 0, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 21 0, .gapLower 1 2, .triangle 17 0, .corridorLower 2 5, .corridorUpper 0 2]

-- Cycle fingerprint 9b483b9b503cf83dd66ef6dcff615b8a4685d4408196495ffbd54f76b0e35620.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 2, .distance 2 6, .distance 2 5]
    constant := ![0, 0, -1, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, false, true] }
  origin := ![.triangle 28 1, .triangle 25 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 18 0, .triangle 30 1]

-- Cycle fingerprint 9eecec3b056218e19ae2b85d97d73da95f629c2d2fbbde60b1cebbaf101746c6.
def localCycle00094 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 5, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 29 0, .gapLower 2 3, .triangle 15 0, .triangle 17 0, .corridorLower 2 5]

-- Cycle fingerprint a0f77d97522bcfba30b3d1ad9a69141272c810c72d804486c099cf30c0190207.
def localCycle00095 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .gapLower 4 1, .gapLower 4 0]

-- Cycle fingerprint a1316f1b8839c73a675568ae2d71c861edcf7b4e734de43506ffdd9849611a35.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 24 0, .gapLower 1 3, .gapLower 4 0]

-- Cycle fingerprint aa8407879d3c503c50899a2bf9c62523e95828a3434b91663d2c005f6be15fd8.
def localCycle00097 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, 0, -3, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 2, .gapLower 1 3, .triangle 20 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint ad1a7120947d75ff62793822b37b674c90ab2f2f135325172fd2631e24b48d68.
def localCycle00098 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 3 5, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 5 3, .gapLower 5 2, .gapLower 1 2, .triangle 19 1]

-- Cycle fingerprint b27441e8756d460699dc7bd57ec0f7c0c57eea4e39f8321021973f0e777be08e.
def localCycle00099 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint b352e6944b48af5a0dc6de627b3890afa42406a801f770b04fd2f2f6e9a85d78.
def localCycle00100 : Cycle where
  length := 15
  data := {
    node := ![.distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 3, -1, -1, -1, -1, -1, 0, -1, 3, 0, -1, -1, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 22 0]

-- Cycle fingerprint b3f1c468ae604f92eb496bacb77ce15421f4a3f76b78cd300577912fbd17fbbf.
def localCycle00101 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .theta 2, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 3 5, .theta 3]
    constant := ![0, 3, -1, 0, -2, -2, -1, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.thetaNext 2, .corridorUpper 0 2, .triangle 6 0, .triangle 16 2, .gapLower 1 4, .gapLower 1 3, .triangle 20 0, .corridorLower 3 5]

-- Cycle fingerprint b6641e05bb824b0804545a96cc00f56f5aab8ba2696075018437b3b55b0c9cea.
def localCycle00102 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, 0, -1, -3, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint c1a6c560baf98a13faf9a3136cd44b848bdce5867c67ac5ce1da63da78d813d6.
def localCycle00103 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint c1d2cf55ff4e071b8036f0e3aca5d838047539fcd280080dff8356cb2a41d4f0.
def localCycle00104 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .gapLower 3 0]

-- Cycle fingerprint c27512d80ebd0e24954f2b92338b708ae4a5b86e732fddc6fc4a79121f134ce7.
def localCycle00105 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint c3494799365361acce34591dd706e04efa918482bf12266e8fd95e03ca95ab09.
def localCycle00106 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 0 2, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 2, .triangle 13 0, .triangle 23 0, .triangle 19 1, .triangle 20 0, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

-- Cycle fingerprint c3caa6e923797e1607ccdeef215fc63a1bb27ff5b7d76a30d894a81408389db5.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint c4beb4a144e98396455670a840becc0496ebdae3a16aa67aadfbc93b1ecb8617.
def localCycle00108 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c8ff02093234d8a4664ba0dceb2eb7997a2e05d0d4cf6c73da535468db64e1fc.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint c985d0f4f5076b466be3df3a59675b63208b0ee64e5b9561a5f8de36f03cb52a.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .distance 2 4, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 31 1, .triangle 28 0, .gapLower 4 0]

-- Cycle fingerprint c9b0e3fc6beee767fb4a493ad477aa22228bbd29932a0483c57f0e2f04c46ecb.
def localCycle00111 : Cycle where
  length := 6
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 5, .theta 2]
    constant := ![3, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 30 1, .corridorLower 2 5]

-- Cycle fingerprint c9d9af8e914a26bde4c08f1afa6371c53364da399775b07a8c39ea9b7c51f6a9.
def localCycle00112 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .triangle 29 0, .corridorLower 4 6]

-- Cycle fingerprint cc2c1ebd291b43dbe81c1fc0a42b5def231af5f306622d83738bafeb821d5918.
def localCycle00113 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 0, 0, -1, 0, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, true, true, false, false] }
  origin := ![.triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint ce19faa6dc5a6132fd57f439170a6199768b2afea48048bc9a52b3c232028e4d.
def localCycle00114 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint d02fdf63ae0c21be9f8e3eb192f7b45322f45cb91cbbb33dba5a1a86ad0b23ee.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 19 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint d09905e2b57ce051b0edb8a2d486d2300b629697f64d04f0d08ac07097510887.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 3, .distance 3 5, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 21 0, .triangle 20 0, .corridorLower 3 5, .thetaNext 2]

-- Cycle fingerprint d3b75167eaef3f7f809611e4dc63848896c2e41b2cef34556cbe09f9938c6404.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .gapLower 1 4, .triangle 24 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint d6d511b7762d5f1bc9fa8e734838897dc9a3f66a89821098fe8c55fb2d3faf0f.
def localCycle00118 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 0 4, .distance 0 3]
    constant := ![-1, 0, -1, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 20 0, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2, .triangle 6 2, .triangle 9 1]

-- Cycle fingerprint d7266ba931a535e8f13c0d09e0f2676c1539aaec2e03f458d1d3d208e4f72c35.
def localCycle00119 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 5, .distance 4 5, .distance 1 4]
    constant := ![-3, 2, 0, -1]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 1, .gapUpper 3 2, .gapLower 5 3, .triangle 22 0]

-- Cycle fingerprint d81854102bb4e5c4307287cfb11762c98b2db843bb1f4df74fd98c962f3f0e6a.
def localCycle00120 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint d821f8b504aa57925f7bbbcce6b1a03caef29afed7851c8a7f032b210c0f8774.
def localCycle00121 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 2 3]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 26 0, .triangle 33 0, .triangle 34 2, .gapUpper 4 3, .triangle 25 1]

-- Cycle fingerprint d926d986d2ea882896c61dfacfb489c6b817e3e1673d2679c51c909e6b27f759.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 5, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1, .gapLower 1 2, .corridorLower 1 5]

-- Cycle fingerprint d9d6f6e72c57bf4f39f9b34e116e3b5a5669ef60a89bd9bbbb6ad9954dc8de51.
def localCycle00123 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5]
    constant := ![-1, 0, 0, 3, -3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorLower 3 5, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 19 1, .triangle 21 0, .triangle 33 1]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00124 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint da9daf8df0306f96c9d9f4fa14cb37421388833ea0ad8fd05faa518222ff70a2.
def localCycle00125 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 2 4, .distance 4 6]
    constant := ![0, -1, 0, 0, 3, -1, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 34 1, .triangle 24 0, .gapLower 1 3, .gapLower 4 0, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 28 0, .triangle 29 0]

-- Cycle fingerprint dae1ffcc9b561bab6f829fd8b5aec9b3df18408e5b4ce1940d1e52b770213954.
def localCycle00126 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint dc5d5a78ffaf8c5352dab58ffd6e7752fd9c0c4f76f83499c3989c2549700298.
def localCycle00127 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3]
    constant := ![0, -3, 0, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, true, true] }
  origin := ![.triangle 21 2, .gapLower 1 2, .triangle 17 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 19 1]

-- Cycle fingerprint dd887980aae9cc40ca5f3a3647de128ec62bbc0c788e662d5ec82eaa198c8d28.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 22 0, .triangle 23 0, .corridorLower 4 6]

-- Cycle fingerprint e1f7e979d1aeee0123054de85cbf96b22a9c3290ba44afcb017f1043708f2ae0.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint e23c3e5edff047fc02a422b8a5bd793b705e84cb96e6670989de02fb81e1ed8b.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint e49ccd498e68c878ed66e5c93f66504d00513db0f4071c0784951be1f7ba2e83.
def localCycle00131 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 0, .triangle 18 0, .triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint e547a2165124cec24819f60fb9e4edfef93281e1def1e45d30a73b1195bf5618.
def localCycle00132 : Cycle where
  length := 13
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 1 4, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, -1, -1, -1, -1, 3, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 2, .triangle 23 0, .triangle 29 0, .triangle 28 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint e639920ee2e2b85d4257a2361307c5d0a1a571b2079095e17feb3d3ade621548.
def localCycle00133 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 2, .triangle 29 0, .triangle 28 0, .corridorLower 4 5]

-- Cycle fingerprint e9c71fd9d08fb13fbd0b0d11022305748d250df3d851a75b147eec44eca1825e.
def localCycle00134 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .theta 1]
    constant := ![3, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .gapLower 1 4, .triangle 21 1, .gapLower 1 2, .corridorLower 1 5]

-- Cycle fingerprint ed21a8c3467851fa9f4ab1b6e5c66ff929a98e1c5da839c8ece043afaad5720d.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 2, .distance 0 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2]
    constant := ![0, 0, -1, 0, 0, -1, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 6 2, .triangle 9 1, .triangle 11 0, .triangle 32 1, .triangle 34 1, .triangle 22 0, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 0 2]

-- Cycle fingerprint ed33793a6ae5ff126db925c665fbae0a8d4e84758e994589589c2cffab215ddb.
def localCycle00136 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 5, .distance 4 5]
    constant := ![-1, -1, 0, -1, 3, 0, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false, true] }
  origin := ![.triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 25 1, .triangle 26 0, .triangle 31 1]

-- Cycle fingerprint ef820a973a8f82242523fbbf062acc5100255a2c896d5d9c1a401af78aff1a2f.
def localCycle00137 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, -1, -1, 0, 0, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .triangle 22 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint f0c0bf2b7cf4c6d62b153318350a722df2aac2d7ff7b8b5a46086a525355c3d4.
def localCycle00138 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 2, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint f23cd3cf85103c84afe1bfbb62fdf5237fc7af2899d6a83a1f335e93060deb38.
def localCycle00139 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 32 1, .gapUpper 4 2]

-- Cycle fingerprint f2540f532f9eb8709c110372dcf666f975bf617256cb5ca11276e169f1d0608b.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 2 3, .theta 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 4, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .gapLower 1 1, .triangle 15 1, .gapLower 3 0, .gapLower 3 6, .triangle 9 0, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint f3d907d13b4e8b7f9aa66c6a245519ec62d2e62b565a0cf3740a637f48fdf359.
def localCycle00141 : Cycle where
  length := 14
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 2, .distance 2 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, -1, 0, -1, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 0 0, .triangle 16 0, .triangle 29 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint f509443447927abb51a7760326e2643d6a13b7e94306637d8308eafab08bfc4e.
def localCycle00142 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 3, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![0, -2, 0, -2, -1, 3, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, true, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 20 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2]

-- Cycle fingerprint f5bd941380f88d93a50f01141bb3a15ea0c586f08ba2f29a4465f528908d9926.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint fa777600f32738a13551444d13fb884f9e6cf6ecf2151b9d0fe46370a3892e0c.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, -1, 0, 3, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false] }
  origin := ![.triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 29 0, .triangle 23 0, .gapLower 1 3]

-- Cycle fingerprint fc81817b37ab1ff310868912dd1214e511719270222f2c2699624a91409bc3a0.
def localCycle00145 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fe66e9452bc88927cf1b255c442f46320edf1bd31e1617ebea752666d3236c72.
def localCycle00146 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 3, .theta 1, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, 3, 0, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 3, .corridorUpper 0 1, .triangle 0 2, .triangle 6 0, .triangle 16 2, .triangle 23 2]

-- Cycle fingerprint ff766b22677ce12c9d51006b9f4adc233d121543198befe0821ab913277772a0.
def localCycle00147 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint ffd5a1f39b4d1f8fe570ac64bc03ac92d5a7b991ddd6777fedf59c283d305e3f.
def localCycle00148 : Cycle where
  length := 11
  data := {
    node := ![.theta 2, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2]
    constant := ![3, -1, 0, -1, -1, 0, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, true, true] }
  origin := ![.corridorUpper 0 2, .triangle 6 0, .triangle 25 1, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2]

def library : Library := fun id => if id < 74 then (if id < 37 then (if id < 18 then (if id < 9 then (if id < 4 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id = 3 then some localCycle00003 else none))) else (if id < 6 then (if id < 5 then (if id = 4 then some localCycle00004 else none) else (if id = 5 then some localCycle00005 else none)) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none))))) else (if id < 13 then (if id < 11 then (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none)) else (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none))) else (if id < 15 then (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none)) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none)))))) else (if id < 27 then (if id < 22 then (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none))) else (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id < 26 then (if id = 25 then some localCycle00025 else none) else (if id = 26 then some localCycle00026 else none))))) else (if id < 32 then (if id < 29 then (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none)))) else (if id < 34 then (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id = 33 then some localCycle00033 else none)) else (if id < 35 then (if id = 34 then some localCycle00034 else none) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none))))))) else (if id < 55 then (if id < 46 then (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id = 45 then some localCycle00045 else none))))) else (if id < 50 then (if id < 48 then (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none)) else (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none))) else (if id < 52 then (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)) else (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none)))))) else (if id < 64 then (if id < 59 then (if id < 57 then (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id = 56 then some localCycle00056 else none)) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none))))) else (if id < 69 then (if id < 66 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none)) else (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)))) else (if id < 71 then (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none)) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id < 73 then (if id = 72 then some localCycle00072 else none) else (if id = 73 then some localCycle00073 else none)))))))) else (if id < 111 then (if id < 92 then (if id < 83 then (if id < 78 then (if id < 76 then (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id < 82 then (if id = 81 then some localCycle00081 else none) else (if id = 82 then some localCycle00082 else none))))) else (if id < 87 then (if id < 85 then (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none)) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id = 91 then some localCycle00091 else none)))))) else (if id < 101 then (if id < 96 then (if id < 94 then (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)) else (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none))) else (if id < 98 then (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none)) else (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))))) else (if id < 106 then (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id < 105 then (if id = 104 then some localCycle00104 else none) else (if id = 105 then some localCycle00105 else none)))) else (if id < 108 then (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none)) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none))))))) else (if id < 130 then (if id < 120 then (if id < 115 then (if id < 113 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)) else (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id = 114 then some localCycle00114 else none))) else (if id < 117 then (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)) else (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))))) else (if id < 125 then (if id < 122 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id = 121 then some localCycle00121 else none)) else (if id < 123 then (if id = 122 then some localCycle00122 else none) else (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)))) else (if id < 127 then (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none)))))) else (if id < 139 then (if id < 134 then (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none))) else (if id < 136 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id = 135 then some localCycle00135 else none)) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none))))) else (if id < 144 then (if id < 141 then (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)) else (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)))) else (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id = 148 then some localCycle00148 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 1, 0, 6, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 3, 1, 0, 6], ![2, 1, 4, 0, 3, 5]], proof := .tail 81 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22144)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![5, 1, 2, 0, 6, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 1, 2, 0, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 106 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22145)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 4, 6, 0], ![5, 1, 2, 0, 6, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 94 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22146)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 4, 6, 0], ![5, 2, 1, 0, 6, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 10 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22147)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 4, 2, 6, 0], ![5, 3, 4, 1, 6, 0], ![5, 2, 1, 0, 6, 4], ![5, 2, 1, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 0, 3, 5]], proof := .tail 51 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22148)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 4, 6, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 1, 0, 6, 4], ![5, 2, 1, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![2, 1, 4, 0, 3, 5]], proof := .tail 17 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22149)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 6, 4, 0], ![5, 1, 2, 0, 6, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 41 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22150)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 6, 4, 0], ![5, 1, 2, 0, 6, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 26 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22151)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 6, 4, 0], ![5, 2, 1, 0, 6, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 4 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22152)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 6, 4, 0], ![2, 5, 1, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 3 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22153)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 5, 1, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 126 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22154)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 5, 1, 0, 6, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 3, 1, 0, 6], ![2, 4, 1, 0, 3, 5]], proof := .tail 115 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22155)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 1, 0, 6, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![2, 4, 1, 0, 3, 5]], proof := .tail 132 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22156)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 5, 1, 0, 6, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 115 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22157)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 1, 0, 6, 4], ![5, 2, 6, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![2, 4, 1, 0, 3, 5]], proof := .tail 22 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22158)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 3, 6, 4, 0], ![5, 1, 2, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .low (![102, 78, 65, 97, 114, 82, 66, 24, 2, 2, 2, 2, 20, 1, 142, 117, 89, 68, 146, 134, 53, 122, 101, 12, 35, 63, 56, 5]) }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22159)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 3, 6, 4, 0], ![5, 1, 2, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 26 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22160)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 6, 4, 0], ![5, 2, 1, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 86 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22161)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 2, 4, 0], ![5, 3, 6, 1, 4, 0], ![5, 2, 1, 0, 6, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 34 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22162)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![5, 3, 6, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![5, 3, 6, 4, 1, 0], ![5, 2, 1, 0, 6, 4], ![5, 6, 2, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 8 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22163)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 33 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22164)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 6, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 29 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22165)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 87 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22166)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 5, 6, 0], ![2, 1, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 84 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22167)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 5, 6, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 29 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22168)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 5, 6, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 52 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22169)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 4, 2, 5, 6, 0], ![3, 4, 1, 5, 6, 0], ![2, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 3], ![1, 2, 4, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 88 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22170)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 4, 5, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 72 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22171)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 4, 5, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 3], ![2, 1, 4, 3, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .low (![44, 119, 98, 91, 64, 73, 85, 137, 23, 15, 40, 15, 54, 140, 62, 138, 43, 135, 6, 37, 36, 118, 45, 83, 118, 70, 7, 93]) }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22172)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 6, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 3, 2, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 46 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22173)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 3, 2, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 46 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22174)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 39 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22175)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 99 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22176)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 55 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22177)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 4, 6, 0], ![2, 1, 5, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 2, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 99 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22178)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 80 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22179)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 1, 5, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 2, 1, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 59 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22180)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 2, 1, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 144 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22181)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 1, 5, 6, 0, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 16 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22182)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 1, 5, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 3, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 77 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22183)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 5, 6, 0, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 1, 3, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .tail 16 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22184)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 5, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 1, 3, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .tail 29 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22185)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 1, 3, 2, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 46 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22186)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 3, 2, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 100 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22187)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 4, 6, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 1, 3, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 99 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22188)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 47 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22189)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 4, 0], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 90 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22190)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 4, 0], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 130 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22191)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 131 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22192)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 1, 5, 6, 0, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 1, 3, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 11 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22193)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 1, 5, 6, 0, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 1, 3, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 18 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22194)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![3, 5, 6, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 1, 5, 6, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 79 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22195)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 46 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22196)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 3, 5, 6, 4, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 1, 3, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 60 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22197)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 4, 6, 0], ![2, 5, 1, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 2, 3, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 59 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22198)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 6, 4, 0], ![2, 5, 1, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 69 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22199)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 2, 6, 0], ![3, 4, 5, 1, 6, 0], ![2, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 3, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 110 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22200)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 2, 6, 0], ![3, 5, 4, 1, 6, 0], ![2, 5, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 3, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 77 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22201)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 6, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 3], ![2, 4, 3, 1, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .tail 110 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22202)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 6, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 2, 3, 1, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .tail 29 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22203)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 4, 6, 0], ![5, 1, 2, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 1, 2, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 32 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22204)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 3, 6, 4, 0], ![5, 1, 2, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 32 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22205)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 3, 4, 6, 0], ![1, 5, 6, 3, 4, 0], ![5, 1, 6, 2, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 116 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22206)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 4, 6, 0], ![5, 1, 2, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 120 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22207)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 3, 6, 4, 0], ![5, 1, 2, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 120 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22208)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 3, 4, 6, 0], ![5, 1, 6, 3, 4, 0], ![5, 1, 6, 2, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 3, 2, 0, 5]], proof := .tail 92 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22209)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 4, 6, 0], ![5, 2, 1, 6, 0, 4], ![5, 1, 2, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 50 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22210)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 6, 4, 0], ![5, 2, 1, 6, 0, 4], ![5, 1, 6, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 46 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22211)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 2, 6, 0], ![5, 3, 4, 1, 6, 0], ![5, 2, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![1, 2, 4, 3, 0, 5]], proof := .tail 46 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22212)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 4, 6, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 3], ![4, 3, 2, 1, 0, 6], ![2, 1, 4, 3, 0, 5]], proof := .tail 46 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22213)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 6, 4, 0], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 30 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22214)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 71 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22215)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 5, 1, 6, 0, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 3, 1, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 104 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22216)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 1, 6, 0, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 104 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22217)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 5, 1, 6, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 141 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22218)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 3, 6, 4, 0], ![5, 1, 2, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 9 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22219)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 3, 6, 4, 0], ![1, 5, 6, 3, 4, 0], ![5, 1, 6, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 116 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22220)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 3, 6, 4, 0], ![5, 1, 2, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 120 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22221)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 3, 6, 4, 0], ![5, 1, 6, 3, 4, 0], ![5, 1, 6, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 3, 2, 0, 5]], proof := .tail 92 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22222)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 6, 4, 0], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 46 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22223)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 2, 4, 0], ![5, 3, 6, 1, 4, 0], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 34 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22224)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 1, 6, 0, 4], ![5, 2, 6, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![2, 4, 1, 3, 0, 5]], proof := .tail 49 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22225)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 3, 6, 4, 2, 0], ![5, 3, 6, 4, 1, 0], ![5, 2, 1, 6, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 143 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22226)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 2, 4, 0], ![3, 5, 6, 1, 4, 0], ![2, 5, 6, 1, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 107 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22227)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![3, 4, 5, 6, 1, 0], ![2, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 3], ![2, 4, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 58 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22228)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![3, 5, 4, 6, 1, 0], ![2, 5, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 29 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22229)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![3, 5, 6, 4, 1, 0], ![2, 5, 6, 1, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 58 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22230)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![2, 5, 6, 3, 4, 0], ![1, 5, 6, 3, 4, 0], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .low (![102, 78, 127, 105, 27, 123, 66, 21, 2, 2, 139, 2, 20, 0, 38, 139, 25, 14, 38, 139, 147, 35, 139, 19, 74, 139, 139, 113]) }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22231)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 2, 6, 3, 4, 0], ![5, 1, 6, 3, 4, 0], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 26 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22232)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 2, 3, 4, 0], ![5, 6, 1, 3, 4, 0], ![5, 6, 1, 2, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 148 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22233)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 2, 4, 0], ![5, 3, 6, 1, 4, 0], ![5, 2, 6, 1, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 28 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22234)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 2, 4, 0], ![5, 6, 3, 1, 4, 0], ![5, 6, 2, 1, 0, 4], ![5, 6, 1, 2, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 111 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22235)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![5, 3, 4, 6, 1, 0], ![5, 2, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![2, 4, 3, 1, 0, 5]], proof := .tail 46 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22236)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![5, 3, 6, 4, 1, 0], ![5, 2, 6, 1, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 46 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22237)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![5, 6, 3, 4, 2, 1], ![5, 6, 3, 4, 2, 0], ![5, 6, 3, 4, 1, 0], ![5, 6, 2, 1, 0, 4], ![5, 6, 2, 1, 0, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 76 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22238)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 5, 6, 0, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 3, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 108 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22239)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 5, 0, 4], ![1, 2, 5, 6, 0, 3], ![1, 2, 4, 6, 3, 0], ![1, 2, 4, 5, 3, 0]], proof := .tail 124 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22240)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 5, 6, 0], ![1, 2, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 3], ![1, 2, 6, 4, 3, 0], ![1, 2, 5, 4, 3, 0]], proof := .tail 61 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22241)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 3], ![1, 6, 2, 4, 3, 0], ![1, 5, 2, 4, 3, 0]], proof := .tail 96 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22242)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 5, 0, 4], ![1, 6, 2, 5, 0, 3], ![1, 6, 2, 4, 3, 0], ![1, 5, 4, 2, 3, 0]], proof := .tail 125 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22243)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 0, 4], ![1, 6, 2, 5, 0, 3], ![1, 6, 2, 4, 3, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 95 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22244)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 5, 0], ![1, 2, 6, 5, 0, 4], ![1, 2, 6, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 1, 2, 4, 3, 0]], proof := .tail 109 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22245)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 5, 0, 4], ![1, 6, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 112 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22246)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 0, 4], ![1, 6, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 57 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22247)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 5, 0], ![1, 2, 6, 5, 0, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 13 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22248)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![1, 6, 2, 5, 0, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 57 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22249)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 5, 0], ![6, 1, 2, 5, 0, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 145 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22250)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 5, 0], ![6, 1, 2, 5, 0, 4], ![6, 1, 2, 5, 0, 3], ![6, 1, 2, 4, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 103 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22251)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 5, 6, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 3, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 133 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22252)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 4, 6, 0], ![1, 2, 6, 5, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 2, 6, 3, 0], ![1, 2, 4, 5, 3, 0]], proof := .tail 124 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22253)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 5, 6, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 108 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22254)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 5, 6, 4, 0], ![1, 2, 6, 5, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 2, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 124 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22255)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 48 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22256)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 0, 4], ![1, 6, 5, 2, 0, 3], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 2, 3, 0]], proof := .tail 67 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22257)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 6, 2, 3, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 42 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22258)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 0, 4], ![1, 6, 5, 2, 0, 3], ![1, 6, 4, 2, 3, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 95 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22259)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 0, 4], ![1, 6, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 2, 3, 0]], proof := .tail 109 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22260)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 0, 4], ![1, 6, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 1, 4, 3, 2, 0]], proof := .tail 57 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22261)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 5, 4, 0], ![1, 2, 6, 5, 0, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 128 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22262)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 5, 4, 0], ![1, 6, 2, 5, 0, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 1, 3, 2, 0]], proof := .tail 57 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22263)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 5, 4, 0], ![6, 1, 2, 5, 0, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 145 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22264)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 5, 4, 0], ![6, 1, 2, 5, 0, 4], ![6, 1, 5, 2, 0, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 103 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22265)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 4, 6, 0], ![1, 5, 2, 6, 0, 4], ![1, 5, 2, 6, 0, 3], ![1, 4, 3, 2, 6, 0], ![1, 2, 4, 3, 5, 0]], proof := .tail 129 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22266)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 3, 6, 4, 0], ![1, 5, 2, 6, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 3, 2, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 129 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22267)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 5, 6, 3, 4, 0], ![1, 5, 6, 2, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 3, 2, 6, 0], ![1, 4, 3, 2, 5, 0]], proof := .tail 31 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22268)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 5, 6, 2, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 3, 6, 2, 0], ![1, 4, 3, 5, 2, 0]], proof := .tail 75 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22269)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 0, 4], ![1, 5, 6, 2, 0, 3], ![1, 4, 6, 3, 2, 0], ![1, 4, 5, 3, 2, 0]], proof := .tail 121 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22270)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![6, 5, 3, 4, 2, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 5, 3, 4, 0], ![1, 6, 5, 2, 0, 4], ![1, 6, 5, 2, 0, 3], ![1, 6, 4, 3, 2, 0], ![1, 5, 4, 3, 2, 0]], proof := .tail 136 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 22271)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (22144 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 22144 ≤ id.val) (hhigh : id.val < 22272) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 22144)) = true := by
  let j : Fin 128 := ⟨id.val - 22144, by omega⟩
  have hsum : 22144 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (22144 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard173
