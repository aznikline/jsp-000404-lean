import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard107
open N4R2OuterLeftReplay

-- Cycle fingerprint 00831c2d22f2620aa1f2d8ed52fbbb02b9a529807758b407ed0685cc89a86bf2.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 1, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 02c72d6d97e55ddec3a17abf55c194638f419c9d6fc46ce8a205422f1f3f509c.
def localCycle00001 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 02df563bebe430fa25355241d6d907e2e20ea9965d35cf6fc1462ebeb663a2ca.
def localCycle00002 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -3, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 04397e005568663154d9297c372e967036e8d5b9b5d2592c2b19d26e5883b59b.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 0, .triangle 0 2, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 05023635789332b4f8a086f99668fc5049f4d8c2ee1945b320f263707a9b06c6.
def localCycle00004 : Cycle where
  length := 12
  data := {
    node := ![.theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![0, 3, 0, 0, -2, 0, -1, 0, -2, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, true, true, false, true, false, true, false, true, true, false] }
  origin := ![.thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 0 2, .triangle 8 0, .triangle 18 2, .gapLower 1 2, .triangle 20 1, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 05a0d7e1c4053534288ebe061b044e32e91f1136c735514561661237ced0bd11.
def localCycle00005 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 2, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 072dbd1a8496f486b5f1040cb0404c828304a358d57f0e7c12f88515c3aa81a6.
def localCycle00006 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 2, .distance 2 3]
    constant := ![0, -2, -2, 0, -1, 0, -1, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 17 0, .gapLower 2 0, .gapLower 2 6]

-- Cycle fingerprint 09411471cea999fcfc96e766775dd424a79f92e21c3074404cbe1e91d2d84df9.
def localCycle00007 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 6, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-1, -2, -2, 0, 0, -1, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, true, false, true, false, true] }
  origin := ![.triangle 1 0, .gapLower 1 3, .gapLower 1 2, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint 0a459f76803996788a83c38f28d44d35504c75a12a5c852abac48b45e9279fe8.
def localCycle00008 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 24 0, .triangle 20 1, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 0d440bd9e6f5b608d1ceef2e04d8b803f009b51b72d626f63980926b2c1e0a68.
def localCycle00009 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 5, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 2, .corridorLower 1 4]

-- Cycle fingerprint 0da9eb76d9f42bcd9cfffe66a730c7986dad2aaa0939841f0eac5108da09c363.
def localCycle00010 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 1 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 0dbb487edde4a9be6ed445068f3fd11de35ea60e4482667facdecddcf6fda1d9.
def localCycle00011 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .distance 2 3, .distance 3 5]
    constant := ![-1, -1, 0, -1, -1, 0, -1, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 33 0, .triangle 24 0, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .corridorUpper 2 3, .triangle 26 0]

-- Cycle fingerprint 0e362fe9ae61a4791313e362f26148dde94d7ee9d8f2cb7c65042ec3d46359a0.
def localCycle00012 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0, .triangle 17 1, .corridorLower 1 2]

-- Cycle fingerprint 0e42ccb32cfa81ff57caef816d2086ada3c4b3b937f17890d3cbe70b8d6e81e7.
def localCycle00013 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -1, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 11bc815749b31aafa9031442105ad39c9c72cecd4ce4a1c8c976567a8004b2e6.
def localCycle00014 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 20 1]

-- Cycle fingerprint 125dd4b5477cc2e7798b894aada10614d903d303e29e6dc70f4b9684dfbc5e11.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 14de00e3f04f30f2221766ebd40cb5e5871e74195d04fed20ab30e6cd57d1c83.
def localCycle00016 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 16529661b1162296b4304e0e2895f54c1a534bde5cdee330b0a2fd43708d1edb.
def localCycle00017 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .gapLower 3 0]

-- Cycle fingerprint 167ec0dee67ba9aa5bbb27aa6d5a71aa628bba96609dfd5205fb3d8ae320e254.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 16e266cababf9ee07f01a9e043b88e19ed66662d64ac533fb2cbbca03063b9a8.
def localCycle00019 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0, .gapLower 1 3, .triangle 24 1]

-- Cycle fingerprint 19ce9296f30b08b558c893e29c45f9b1c2aee0433fcdcaa9050d2de8277ef5a1.
def localCycle00020 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 1db3e60012160e3ffecbbe6816292922d8c122562fcc93eeefed0a8205aacb55.
def localCycle00021 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 1df81cb83c0d659dad28f98d1bfb740512baac3a7ed43e603a8dd4ea556cb2cc.
def localCycle00022 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 1ec3182d335d2c9cb7472e31490f675f0ae113d2a1295cd95c0f6d746224763a.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint 1ec7c15c4e723026f353c495ec49494e2fcb6e5f3a4930d560165a3c776ca167.
def localCycle00024 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![-1, -1, -1, 4, -2, 0, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 7 0, .triangle 17 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 0 2]

-- Cycle fingerprint 1f66d6223654d2407a1aa978c374479709a3c8758617e686dae26b7e1c16f3d3.
def localCycle00025 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, -2, -1, 4, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .triangle 23 2]

-- Cycle fingerprint 2054f186eb5759c615aabe9e1c5487a3a21b06e35bd82cbcb7cd098b9638a54f.
def localCycle00026 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 0, 0, 3, -1, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 16 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 24 0, .gapLower 1 4, .triangle 1 0, .triangle 2 0]

-- Cycle fingerprint 206c702a3497f231fb223c86e19a2d1bb0f1374edfa1f7dcd1f818286df3d436.
def localCycle00027 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 4 0, .triangle 24 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 20d8dbe4b51a365b485b601e1f35be30c8e8161ea12c0c2947851fc048120019.
def localCycle00028 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, -1, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 4 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 238d200ffe99e679d3cb48086f3ca05d9a5f7269fd24a0bcdcccb6d450de67e7.
def localCycle00029 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 2492eeb5f9e1d79de6273aa2e7ac66a9a753716cc86650a33cac37404d79d99f.
def localCycle00030 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 0 2, .distance 2 4, .distance 1 4]
    constant := ![-3, 0, 2, 0]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, true, true, false] }
  origin := ![.gapLower 1 4, .triangle 0 2, .gapUpper 2 4, .gapLower 4 5]

-- Cycle fingerprint 24a20c9f4e2f4c76c99ec0458a559761cc3ff989a53913cb9781931ed59af8c2.
def localCycle00031 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![0, -2, 0, -1, 0, -2, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 23 2, .gapLower 1 3, .triangle 0 2, .triangle 7 0, .triangle 17 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint 2507debf859e3394e04e5afd78a279b6f9b3b000863d2b817defad6e53536f4a.
def localCycle00032 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 26cf7576f7f6720d828ec6103752ece1271c262fbaa1866f936cf0cb2441fce9.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, true] }
  origin := ![.triangle 8 0, .triangle 30 1, .triangle 17 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 0 2]

-- Cycle fingerprint 2708623127860260d0dbc7be8dad77b531e971f74b18ad55b2e38c6148bc23df.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint 28ce7314b54975ae1675b032ed204fb31163e13dcb99d24db953f84746c98716.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6, .distance 3 6, .distance 3 5, .theta 3, .distance 2 3]
    constant := ![0, 0, -3, -1, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, false, false, true, true, false, false] }
  origin := ![.triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .triangle 21 1, .triangle 33 1, .corridorLower 3 5, .corridorUpper 2 3]

-- Cycle fingerprint 2953a584f3c741bdfa6f356145664939592056898fbcdeee677de551f161613b.
def localCycle00036 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 29fb2751dda0b3385cc95ea617d8d79ed0ab9e0c9c66137cbdc3b0ae92cda251.
def localCycle00037 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 2a3d2b2b2dabe0d167bf26b67442ec5ef5372f685e7810edf3aee8f1501e7711.
def localCycle00038 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4]
    constant := ![0, -2, 0, 0, 3, 0, -1, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true, false, false] }
  origin := ![.triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 2b42e7bba8c20135666bf3b358fa268630b25eef7fe08ce07b10ed3a0811961b.
def localCycle00039 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, -1, 3, 0, -2, -2, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 20 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 3 0]

-- Cycle fingerprint 2d1be1d9059e6ed093b400478f2bcc0854363c973d1a697fb2e57a9f3e06f923.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3]
    constant := ![0, -2, 0, 0, -1, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, true, false, true, false, false, false] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 2da1154b8917bd075066ca6a639b87d3ab0c8a4b5f6d2d4f80344a3f65341078.
def localCycle00041 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 3, 0, 0, -3, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 305f236863c407eccb4e42995a8129f441295c3bdff0461db83404cb8b292a0e.
def localCycle00042 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 3 0, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 31897c56029cad3f47957c1c2fd7fdd3bf5e1fb71924043a9ab7f0b199b5b022.
def localCycle00043 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, 0, 0, -2, -2, 0, -1, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 35fdf44e0fcede763ffad383207bca7c44efcba6fa02763afb455ea65c46c5dd.
def localCycle00044 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 361ac8a7d7ab1a359eea71b9e19dfc4fa1ce6262c2f3bd98b75bbdc527d4664e.
def localCycle00045 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 2, .distance 2 3]
    constant := ![0, -2, -2, 0, 0, -1, -1, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, true, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 0, .gapLower 2 0, .gapLower 2 6]

-- Cycle fingerprint 37190aa3a2286e2ba8630918ae3853fba82eff3490fb2fc627fe514b4767ce80.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .triangle 24 1, .triangle 17 1, .corridorLower 1 2]

-- Cycle fingerprint 37dd48e5975766029c0e8c99d8c981e82b75b7b73c6afd7f8c0b579277b623bc.
def localCycle00047 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -2, -1, 0, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 3a4ef44d5a867614ebec6f0fd1c02c69a61955bd8143e4ab7facd339c6d2bef1.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, -1, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 3bdeffd485030e33d95fb44eff0cb364f2ebfc04749c9fc10d8230330c457112.
def localCycle00049 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 6]
    constant := ![0, -1, -1, -1, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, true] }
  origin := ![.triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 4 2]

-- Cycle fingerprint 3be102b955c3c8c43e4a3c5f5e9136b065333af092ca7928e36e86be7bb24827.
def localCycle00050 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 3c4032fe4bda397f34df816b6ff9c8d7e1518490fa387c2773661eb7985a23c6.
def localCycle00051 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 24 2, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 3d1258175823ee6a632952fe635ccd60c1f66f8c1f89e5a1404a7948529b6387.
def localCycle00052 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2]

-- Cycle fingerprint 4320bcc3bc6e70dc1067e1d20a58b114cc395b8ce31985eaa8dfa564cf0c4266.
def localCycle00053 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint 433e1b6214950fcc243e730fdef545ecabff3783ac4e643fb9e663be77bdb0c7.
def localCycle00054 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 3 4, .theta 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 4, -1, -3, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false] }
  origin := ![.triangle 19 1, .corridorLower 3 4, .gapLower 3 6, .triangle 20 0, .gapLower 1 3, .triangle 2 0]

-- Cycle fingerprint 48d7b0b20f4ce559141baf82fc872359f7297885ee661fe1310efd5b4e69719a.
def localCycle00055 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![-1, -2, 0, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint 4a165f5a037c561b00e20c4e73b21adc029a1cfdad2f75455166a41e202a12a9.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -1, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .gapLower 0 3, .triangle 8 0, .triangle 30 1, .triangle 17 0, .gapLower 1 0]

-- Cycle fingerprint 4dda35d2f9bc16dc59fc3e880ba3b90c9eb351ef9c708d20aea6a34c62fe41da.
def localCycle00057 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, -1, 0, 0, 3, 0, -1, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 4fb95911f5ceadc60bd2db46eb72ab8b994c360a74ef02c8b54f067b6576a33d.
def localCycle00058 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint 50b06981b9df6dcc2bba525fda748db9d6e505ca67848795bb2b48ab6e23a46c.
def localCycle00059 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5]
    constant := ![-1, -2, 0, 0, 3, 0, -2, -1, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 0, .gapLower 0 3, .triangle 8 0, .triangle 30 1]

-- Cycle fingerprint 50dfcbb74eea949ca4add866ac8440b1b968f2097c7297a333f1db9c71d32241.
def localCycle00060 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 1 6]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 5378363ec106d483b311369d7fe123bebd563666eb73cb5fa6af332d7af9fa91.
def localCycle00061 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 53c72a7156d6bc2d98cdc894a639581e4ef6e2fa35f89b147604429e7340f0d4.
def localCycle00062 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6]
    constant := ![-2, 0, 0, -1, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 560613d40c55893dc712ad8d17265710ca08e6b0c652c177b132c634b949876c.
def localCycle00063 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6]
    constant := ![0, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 24 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0]

-- Cycle fingerprint 5630279542a85ecd0f50acdc163eb0b6c559db363e5aa2f74cec01f637449445.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 2, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 56f70a0340497caefe582f6879b691209e45adf5e951dfbe12d20f487875ef3c.
def localCycle00065 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 58682d73a681e9f7dc434fbc957693bf8b1bd01030fb2f85a901862b23eb3689.
def localCycle00066 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1]

-- Cycle fingerprint 58732fd74c7ca954f9d26dc72b7da2ec1337998416b27600bdd0c0a733f1db57.
def localCycle00067 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 33 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 59a0387085d3b32404f477bbd710673b5b62b44280e928c2d6214c211b143163.
def localCycle00068 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 1 3, .triangle 18 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 5a21420a4b4cc1ccb58e45a527093e3f3a8dfbc9a4a8edf31108e1ad06e34616.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, -2, -1, 4, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint 5b6ae0e8583050490f5b7e7ff2e370a4499236ae28a760d6d80ff54b12f6e560.
def localCycle00070 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, 0, -2, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 1, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 5b8217bb2be660512ff392aa7452e0fe18fb766868bb9086e68f90f83d1cbc25.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3]
    constant := ![-2, -1, -1, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 2 0, .triangle 4 0, .triangle 24 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 5d2238e6b9c7381dff3ec77b014a668087789543a7550fc32c70efe4177e8ffa.
def localCycle00072 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -1, 0, 0, 3, 0, -1, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 5eb9b5f9f5d86b026b4617a75e8ff5f587546331f1f2cd89263b6a78efb9d9ea.
def localCycle00073 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![-1, -1, -1, 4, -2, -2, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 7 0, .triangle 17 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .gapLower 1 4, .triangle 4 0, .gapLower 0 2]

-- Cycle fingerprint 6003f4ce0127a9d6922df755ffbe11a5a6467f56a53379b17d1bd8bd712a5f2e.
def localCycle00074 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 24 1, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 604847f536476abf978f8da725f74a5bca008bf50b71fd07b3a162a2a1425f81.
def localCycle00075 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 61b1022a00b8defcf06afd21e5fdfeb80eff0b3b46c1eb22770de162fc9b11df.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 18 1, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 61ca4377a6489d8055a770e476ee1384b99f54a8dc2ee6ef7fc1032f99d85a9b.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 24 2, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 61e37d1047d58cdf4bd8d04c7084ae6e988a38320ecd0093a93ddb305b39ff27.
def localCycle00078 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 649c1741d7f99aeae7059a268f1fb888e3d7f5b0293d4686526f77df119c31fa.
def localCycle00079 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 1 0, .triangle 2 0, .triangle 16 1, .gapLower 1 0]

-- Cycle fingerprint 64d7d1c8e7c1c5e071b50756408c1bbba90bc7e500487fe388b935d16d63e62c.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 654fbbd66de5fedec1d7d772bbfedf518b7af5d357aed1c6872994b982c3948d.
def localCycle00081 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 30 2, .triangle 29 1, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 6667ee4cdcb5e4f8dd88ba25c52dfaccba0a3844cee25cf309c65bb189b325c7.
def localCycle00082 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![0, 2, 0, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, true, false, true, false] }
  origin := ![.triangle 3 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 15 2, .triangle 1 0]

-- Cycle fingerprint 668ca9ebf75515b6aeba8fbe5881e9a48410da4a175febcc91a21dda7f8b4db4.
def localCycle00083 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5]
    constant := ![-1, -2, 0, 0, 3, 0, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, true, false] }
  origin := ![.triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 2, .triangle 8 1, .triangle 7 0]

-- Cycle fingerprint 67c827a4f419a214e2b654a8325fb6a2efd166a141c01dbc47d4c58faee8d6e4.
def localCycle00084 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3]
    constant := ![-1, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 1 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0]

-- Cycle fingerprint 6cd4b6fad5dcca16c38d927003be24023e65d9071f64d88cbe005a1193d2481b.
def localCycle00085 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .gapLower 1 2, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 6cd85e8606e5eb530201313c44971bd50def497feb1d5906b33a3b6178ca38e2.
def localCycle00086 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![-1, -3, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0]

-- Cycle fingerprint 6cec15dffd67785ec6f830a2489597d51cf88e6a9c90117ac1e429204f44a42e.
def localCycle00087 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 1 5, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .gapLower 1 2, .corridorLower 1 5]

-- Cycle fingerprint 6dbedc0335021f78e7b494269ee26de9bc6c825da7780f48d2b9ae030455c807.
def localCycle00088 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 24 1, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 6f7ed5e649151e36d03c19621bc54217d4d14233f22dd98f0dc7076faea1324b.
def localCycle00089 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -1, -2, -1, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 33 2, .triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 1 0, .gapLower 1 2, .corridorLower 1 4, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 70100fe8a94e93a6736c25e1fbfa568fa1df7b6066054b646005380ceb23e519.
def localCycle00090 : Cycle where
  length := 7
  data := {
    node := ![.distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5]
    constant := ![-1, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .triangle 7 0]

-- Cycle fingerprint 70d8edd0fa2c844ee3511f73a6f40d68fcfec7e6118042ceab9e8696cb521050.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .corridorLower 5 6]

-- Cycle fingerprint 71081e72581cf9c1c7f2e40c70760e76dfb6cea1f0c35e013df444ff59f621a0.
def localCycle00092 : Cycle where
  length := 13
  data := {
    node := ![.distance 3 6, .distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 3 6]
    constant := ![0, 0, -2, -1, -1, -2, -1, 0, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, true, false, false, false, false, false, true, false, false, false, true, true] }
  origin := ![.triangle 27 2, .triangle 18 2, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 2]

-- Cycle fingerprint 720b7293df6542c5ce01e995317d8ea59d8e96c64df34e81da474a7eb39e6bd3.
def localCycle00093 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 3 6, .distance 0 3, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 21 0, .triangle 11 0, .triangle 9 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 73b1b1bbc4feb2fc81a4c7a0959fdcb490fccaf0a292a937d97cd6e33e3cfaf2.
def localCycle00094 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 3 0, .triangle 17 1, .gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 74baf21f29db27a3836ecb2341b59d470742e0d53aa7b01082c3d2f93cfc5571.
def localCycle00095 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 2 1, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint 759e7f0c846eb8157efaf4a3493913f7d4ea3bb2dca46b55ceba3993866a3963.
def localCycle00096 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 774c55349f81aec08ea5de3e4defb74a7236b7b253b6616fe412fb6299305c1f.
def localCycle00097 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 2, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 7a09075281b67dba3355668d0d06894ca6dedab756edcd5969d463914f0480a4.
def localCycle00098 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 2, .triangle 13 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7a6d8d8a3286876e65367cb034d9c5410bc1747bed3d7450d1fdc9814c92d0cd.
def localCycle00099 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 7ad1c105573d54d5d2a75516068ec30efaa593cced05230fb6daa533e2d83d80.
def localCycle00100 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 23 0, .triangle 2 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 7b34010d047c2bb886d8f792b1b59859558ff7e2d594bbfa42349ca3f3ed214d.
def localCycle00101 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 5, .distance 1 2, .distance 2 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 3, .gapLower 1 1, .gapUpper 2 1]

-- Cycle fingerprint 7bb5a3442fc42a4b1309781534dc8a1dac7e78dabb5c3f115c01e767eb0d2166.
def localCycle00102 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint 7be376acc0d491a2fd62c45bea77368ad8671c18c99e7a699fd2eef684451bf1.
def localCycle00103 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, -1, 0, 0, 3, 0, -1, -3, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 7e7f597fc71ac72bb9a141bbea620069cd844ff34283926e6ee2d403f274d420.
def localCycle00104 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7ed4eb0ad65b81018a3292fbfedfe268a69dd7fd4af478e8af4fc6dbcf3190be.
def localCycle00105 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, 0, -2, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 80050d350c02023a825eb1df6c3349dee000d7b966efb470b5d76fa90c974b3c.
def localCycle00106 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 23 0, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 804bce623dac8db57b5a5d71e53b02e1ed7dd62259f86de055e50e8511889b82.
def localCycle00107 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8244f1119fea1703b681b6e482b0f7e2ea2eaf3da76aa40fca6fa70d5aea2898.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 82dc44d477fdeaa791fadb7e5c910d3aa46eefce10232689e531dba20cbd5dcd.
def localCycle00109 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 34 1, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 839785915fcf58e2638bd87a4fa72b0498d0be967285957abfddaf46f0c7507c.
def localCycle00110 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 841ca40ae368f414497e1ab7df3dadc685fcb6075b68b1127946efea7e0b6d0d.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![-3, -1, 0, -1, 3, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .triangle 20 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2]

-- Cycle fingerprint 853a8abd2324a7cd6c58f3e316c330345eba8e7f9cabcfd7e995381a4bde0fdc.
def localCycle00112 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 5, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 17 2, .triangle 20 1, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 85aadf5970a4413006b3a58334bce56b9fc4a8ee922eda09d49cf756dbd1688d.
def localCycle00113 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 0, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 85c5c33b9b4a2f62d5a851aaaa218098c47ff351c2c2edb078e63f1138968d28.
def localCycle00114 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3]
    constant := ![0, -2, 0, -1, 0, 0, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, true, false, true, true, false, false, false] }
  origin := ![.triangle 19 2, .gapLower 1 4, .triangle 0 2, .triangle 8 0, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 868c03ef4b572bcb1ac8842a4935169cd0b0b8d3786377e60b3260a96b2fd85e.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, 0, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0]

-- Cycle fingerprint 87e9fc5b4c43af03beaac03304fdfcb15ec013ffafcb8445f7912e84ad301501.
def localCycle00116 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 88c49b8c65043b09651193e3ed73b230455376896aa9d92e552a68824615b528.
def localCycle00117 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, 0, 0, -1, 0, 3, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, true, false, true] }
  origin := ![.gapLower 1 3, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint 88d0a77f1a6299737767cddfb06f62ef4a4eafcaf21bdfe977bacafdc4bdfe45.
def localCycle00118 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 0 1]
    constant := ![-1, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 89621412ec700dc8e70103423ed2a959ccc5e6d6583ee102dfafff8fe6002524.
def localCycle00119 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 1 6, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 24 2, .triangle 4 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 89fa30a243a0ee5fa00a1081beff4c535e1f976bb14653f1950de15a9225c1b2.
def localCycle00120 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, 0, -2, -1, -2, 0, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 2, .triangle 16 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 89fad01c638b2702e97c419623e965fda7a65133bef31049e88e9ba33c3cdc83.
def localCycle00121 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![4, -1, -1, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 4 0, .gapLower 1 2, .corridorLower 1 5]

-- Cycle fingerprint 8a06ff3abeb03b152df3d870ee24eb4b99c2f4214c9ef293b1d40287a25f5628.
def localCycle00122 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -2, -1, 0, -1, 0, -2, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .gapLower 0 2, .triangle 7 0, .triangle 17 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8c887e9b6dc9526979d75cb0b1cfb57bc51b22497e28801543e8e4aef2a61f69.
def localCycle00123 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 8ca4a7d7aec4f3e3edd7c18e043d0c81ab07e2d44c6180fe7bcb31f06e2637e3.
def localCycle00124 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, 0, 0, -2, -1, -2, -1, 0, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 8cd0fb99c4fc56001eeb8a7bd695081f7b7dea70fca8e7d20e168322d049cc0d.
def localCycle00125 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 20 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint 8d6293b02e6faf34afab2851e67dd0e361f07cc4a3773abd6a1e4d84d6a481b0.
def localCycle00126 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 8e00644b21024a745b6e000fe94155cb7710f8e2ac7fedc29ec3727aae0db26f.
def localCycle00127 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5]
    constant := ![-2, -2, -1, -1, 0, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .triangle 4 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 8fadfc2998849cd72a97133556a71d8b98a891ac6f74d24d81da16ca52842a2b.
def localCycle00128 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-3, -1, 4, -1]
    coefficient := ![0, 0, 1, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 8fb9bad8f9e02d1f42fe96dbae4ce899d5d47c101057f12c69cdfb69e1dfbd40.
def localCycle00129 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0]

-- Cycle fingerprint 904572d30464867e102691de76bc8df22aaffa8deeb564665c2b5834ee821c96.
def localCycle00130 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-1, 4, -1, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 1 0, .triangle 4 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 90b6e5440c42101a10d86639cac43898df0edb1e2608be8dc17a0e5278cd64f4.
def localCycle00131 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![-1, -2, -1, 0, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint 91b4bb854062510c29be856dd3cf42c97a6425b30e1186036fa8082f65a2ba97.
def localCycle00132 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 91ebfcb1ca295c9c0fad035f6eb1236a5c1c7698c5b9ebcd8ee4fbb0ceb981be.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint 927d9c90cdfc30cf967d7ef24e00578bb55477f7b67d294f41150c2d76dda5c6.
def localCycle00134 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 0]

-- Cycle fingerprint 96186db22f95aec15f9809b909505873f6e7f0d4bda05910dc6913134b16559b.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint 961f49252daf24baa7f256661c3118f9907b4e623926018a1f5b15f384675810.
def localCycle00136 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 5 0, .triangle 8 0, .triangle 30 1, .triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 96d5640f0b9eaa1e1d94e9e5f2fe07d68387608502bc53aee1d7aecb696b2d53.
def localCycle00137 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 974d7e3faf1e89b62f13e15fe79188ef88021cabb4756c7559e89139b886420a.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 98cf250e6b9af6c3af8fb66dfb9f27fa040a974303688c9574d33f29e0c34296.
def localCycle00139 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6]
    constant := ![0, 0, 0, -1, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false, true, true, false, false] }
  origin := ![.triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 98e564f78cbfb5aa0f68e347d555ce825172b76fb517b2019b72695fb640ef73.
def localCycle00140 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -1, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 990c3cf2c69e8005ef9ea468e30a8d67e8f83df701b1b9560c4944ff4dc9c6fd.
def localCycle00141 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, 0, 0, -1, -2, 0, -2, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, true, true, false, false, true, false, true, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 27 2, .triangle 18 2, .triangle 4 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 9a5735d316be37b91b56c3b25ad900f70ceafeb554e0b072c63f302ae6180c34.
def localCycle00142 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint 9adb7c41f9ba81fae5673fce37e1723c0b6b5a8dc01c503db139ba746a195d3a.
def localCycle00143 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.triangle 4 0, .triangle 24 1, .triangle 17 1, .gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint 9ae37556b5bf078f7847f41564f99c7317567a25d1ee193abc88057b9f89a1e5.
def localCycle00144 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6, .distance 3 6]
    constant := ![0, -1, 3, 0, -3, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 33 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 0, .triangle 4 0, .triangle 21 1]

-- Cycle fingerprint 9b3218ef7986d387acfaf258d6d4831480f58c88560d1e5c95d0ad00db86de8a.
def localCycle00145 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint 9c2bf83d6e847dd60092e9186653546bac3c6ee8d14ec9bcdd71eb7c250548a4.
def localCycle00146 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint 9c9ccd8e98798166eb4ce9ce73274e92c41c4a39cdcd37ee5d8d76c24a1f0155.
def localCycle00147 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-1, 0, -1, 4, -3, -1]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false] }
  origin := ![.triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint 9d187c994b1d23ca509c6e8f18b8844b9c80f5b744a078bc4546decb2e681b53.
def localCycle00148 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, 0, -1, -1, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 9d4b42a356fa71ca3b918fd7be5e6469b948ac962ff181ead6c36ac6575874de.
def localCycle00149 : Cycle where
  length := 15
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 4, .distance 4 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3, .theta 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, 0, -1, 0, -1, -1, 0, -1, 0, 0, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, true, false, true, true, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 2, .triangle 29 0, .triangle 23 2, .triangle 4 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4, .thetaNext 2, .thetaNext 1, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 9d544248dcc4b3a541e78702cc875ba2f621e494ac0690705c60e072406d97d0.
def localCycle00150 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -2, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 20 1, .triangle 21 2, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .corridorLower 1 2]

-- Cycle fingerprint 9da6151e77eb30ba26904db541c68914c93e7ac49ae7340fc8579db90205b4cd.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 2 0, .triangle 4 0, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint a114e10eb331a92b820653a1996f2f2a174684b4cfc3f10d959f62d857ba16e8.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 3 6, .triangle 5 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 33 0, .gapLower 3 0]

-- Cycle fingerprint a4f460885cb2fd420135b3991c1f2c45e5b7a6f74672a4345a877be71718573f.
def localCycle00153 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 6, .distance 0 1, .distance 0 2]
    constant := ![0, 2, 0, 0, -3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .gapLower 6 5, .gapLower 6 4, .gapLower 1 3, .triangle 0 2]

-- Cycle fingerprint a6cd727050c30e91d13e90b52e11865748616ced8189d6d118af375097e2e26c.
def localCycle00154 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint a6f83c6ecfac060a28c2327f9b6104b92e65f86484b79a6a3065a4a665a007e0.
def localCycle00155 : Cycle where
  length := 12
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, 0, 0, -2, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 17 2, .triangle 24 2, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint ab218b5ff869ade37eed37abb65f0baec4bb9ef742209447fdfdd3d8692a31d5.
def localCycle00156 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 4]
    constant := ![4, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.gapLower 4 6, .triangle 34 0, .triangle 33 0, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 19 1, .gapLower 4 0]

-- Cycle fingerprint ab24b230d80373427d99831c8c34248e2d9f2f84588562b83ed14cb1443bb5a5.
def localCycle00157 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 4, .distance 4 6, .distance 3 6, .distance 2 6]
    constant := ![0, -3, -1, 0, 0, 2, 2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, true, true, true, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 4, .triangle 1 0, .triangle 2 2, .triangle 6 1, .gapUpper 2 2, .gapUpper 4 4, .gapLower 6 5, .triangle 27 2]

-- Cycle fingerprint ab8a59dbe9571c1bdb2ec2cc23d897c40b58b2c5ad2ce0d43100ccdffe40ea8d.
def localCycle00158 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 14 0, .triangle 34 2, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint ac1f5b25cc549e5491d0a34ddd6a8b22a452bb85a494a406a1243b5cc605dd3a.
def localCycle00159 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint ae162d1e8422ec5e5e42236fe5194be06ee1d66db480812a9260ad1c1abfb37b.
def localCycle00160 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 0 0, .triangle 18 0, .triangle 29 1, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint afc58025c3760b3f2b7b9a8c79b2c461a6eed97b12e724e98a3c93400765e9d1.
def localCycle00161 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 30 1, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint b025b33ebbbd7cf21d70f6c2de0f27ac072314e3ecbe8860e547240a618a0f02.
def localCycle00162 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -2, -1, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 15 2, .gapLower 1 5, .triangle 2 0, .triangle 3 0, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint b1297e3c28f599d71428b58ee217a72171cd0f5f261ee7fc6c979e3b586cf96d.
def localCycle00163 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![2, -2, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 2 0, .gapLower 0 2, .triangle 7 0, .triangle 17 0, .corridorLower 1 2]

-- Cycle fingerprint b189ca5884cbc5f16eadf2ea105ee101d2482ef738086e20ae3d7ed74d0d55d7.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 24 1]

-- Cycle fingerprint b18f4e60c9a3a40e3aa6b81d4375715e9a167bd4a3997a5914b514f5f27720fe.
def localCycle00165 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 0 5, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 14 0, .triangle 3 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint b3db53c87129318b8922dbed9ce5fac6bba0ba681c736985eb00311b2451b693.
def localCycle00166 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint b419c01947343ab02abaf5ab04fe0b24c10ed81c88f6dbc63effd0639fa6cc33.
def localCycle00167 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, 0, -1, -1, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 0 2, .triangle 7 0, .triangle 17 0, .gapLower 1 0]

-- Cycle fingerprint b4f334e3948a5091250159a0b4aa113420a791dc5533a047c244913cd89752bf.
def localCycle00168 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, -2, 0, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true, false, false] }
  origin := ![.triangle 4 0, .triangle 24 1, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint b62db70a0727aae1f96f6d8ed867d25af35c7bfac865455d28482e8398b5eba0.
def localCycle00169 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -2, 0, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .gapLower 1 2, .triangle 17 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint b63409054f2b294cb3e02abfb6c9591142c873921339687bbec0d982177a29b0.
def localCycle00170 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 1 3, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 1 0]

-- Cycle fingerprint b6ad9297d95e14d85aac60498f3096ff75d7525433bd1c4ff69bb837a309502d.
def localCycle00171 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5]
    constant := ![-1, -2, 0, 0, 3, 0, -2, -1, 0, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, true, true, false] }
  origin := ![.triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 0, .triangle 4 2, .triangle 8 1, .triangle 7 0]

-- Cycle fingerprint b994de440e67c81af14a4b09f068bd376880cf9fcd9548fbf49a4d1a78616efc.
def localCycle00172 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 27 0, .triangle 26 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint bd7698e3d5b7280631814189489ed45e737173d628d2630ff2a6ef1abde550f4.
def localCycle00173 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![1, -1, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .gapLower 0 3, .triangle 8 0, .triangle 30 1, .triangle 17 0, .corridorLower 1 2]

-- Cycle fingerprint bebb0b103eb77d6d9521484d14d91fcb20f1d1b8fa44095d738c48371cefa861.
def localCycle00174 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, 0, -2, -1, 4, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 24 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint bec3e80403b2dc863fe4ba8d6ddc46bd78a9082a2ae6024502d39874fa3e7f51.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 2, .triangle 21 0, .triangle 1 0, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint c012aab712c2a77b8a962d126788786d98e912bb604d3b3c8811e9b6a508a772.
def localCycle00176 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 4, .distance 0 1]
    constant := ![0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 3 2, .gapUpper 5 5, .triangle 34 2, .triangle 29 0, .triangle 16 2, .triangle 2 0]

-- Cycle fingerprint c01bd7bad2fd39cf237c77c6b8d79854b9ffa569df713b3c7b3c0daa22b11418.
def localCycle00177 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .triangle 24 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint c0f477bc8ec7749aa30b0bee2f402359701c70cf220c5631ba7912d90c334bc9.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint c250c173a1abaf6cccd119cabe765cbbaac1b43d539cee949336dbcd377ac188.
def localCycle00179 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5]
    constant := ![-1, -1, 4, 0, -3, 0, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.triangle 17 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 7 0]

-- Cycle fingerprint c2e023fa00d0f42138a2b3263ba78af6421352e4f6bcb4c3ec2e91be6ba4ae28.
def localCycle00180 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, 0, 0, -1, -3, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 2, .triangle 18 2, .triangle 4 0, .gapLower 1 2, .corridorLower 1 4, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint c3921273d758dc667eb690f75c697c51e9ad1a85f678d20e782bb3662a982f86.
def localCycle00181 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.triangle 4 0, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint c574f80d67809a547cacc6da4c75b705f8c51220c66eecce56c43e11e1b95e85.
def localCycle00182 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, 0, -2, 0, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 0 2, .triangle 8 0, .triangle 30 1, .triangle 17 0]

-- Cycle fingerprint c622584ff72226363e8e1c9e4d1880f6bd77eabcb1bab88bf8327d3d0bb12085.
def localCycle00183 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1, .distance 0 4, .distance 0 2, .distance 2 6, .distance 1 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0, .triangle 2 2, .triangle 6 1, .triangle 8 0, .triangle 18 2, .triangle 21 1, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint c626de3b156f27b76ce76f28c719b84dfe7d6bcfb10839c508f2ae0fa4d36cd4.
def localCycle00184 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 6]
    constant := ![0, -1, -1, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, true] }
  origin := ![.triangle 8 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 2 0, .triangle 4 2]

-- Cycle fingerprint c82b914e6fc7a6cbf06cc58e31bb574df9461d8c487679dc31650097e368f1b5.
def localCycle00185 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![2, -2, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 6, .gapLower 1 5, .triangle 2 0, .triangle 4 0, .triangle 24 1, .triangle 17 1, .corridorLower 1 2]

-- Cycle fingerprint c920072ec595f9f208e0af2153aa38bb05591c3f6032a4e9e44fc7e0b211aa69.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 3 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 32 0, .triangle 31 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint ca6ad3cd8a0015698dc4697ee855b937e83bcec8ebfac623c524e171b6fc6240.
def localCycle00187 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![0, -1, -1, -2, 0, 0, 3, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 0 2, .triangle 7 0, .triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint cbfbd49828e5aa826fce7846219f02b91340312b60510a8a78d0260047ea4307.
def localCycle00188 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 6 1, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint cc022f04b1e59962f4279d8c691e8aee6cc65d8a7814b69fc2b825ecee2c11ff.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, 0, -1, -1, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint cc39beede4c8fae2fbcbb5ad64ca33ac35f53015f77aed0f1445959f10cba878.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -2, -1, 0, -2, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 20 0, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint ce5e1f87c2f64f6f63fb69b58d3bd30673cafe95be3e7de00f18622d0943be37.
def localCycle00191 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint cf8ba0a63f1d9e59021e039383312974c3d5e5b041760f22226a10754b77f7cc.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint d0d1dcc4e7426052b0c82aeac1ab16e542f199a080172d938fe83a0fc53cf001.
def localCycle00193 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint d16799cdde3df2f04a654a5208384c466c6985fb8a4540910d8a7fdd5e61b24b.
def localCycle00194 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-1, 0, 0, 0, -1, 0, 3, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, true, false, false] }
  origin := ![.triangle 4 0, .triangle 21 1, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint d28e124dc20a6fe1cc21729c20fe1614f1b56451ff415b086020b1b95b835278.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 4 6, .distance 3 4, .theta 3]
    constant := ![3, 0, -1, 0, 0, -1, 0, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, true, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 1 0, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 18 2, .triangle 23 1, .triangle 32 0, .corridorLower 3 4]

-- Cycle fingerprint d38c142af49db8215389447ab4bb9ae8d17340a910b1f03563dbf28e5ac2c97d.
def localCycle00196 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, 0, -2, -2, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3, .triangle 0 2, .triangle 7 0, .triangle 17 0]

-- Cycle fingerprint d3c8f20b06d2a3f5352eab35198801c0b1e484333b31bed23699114e9d840c6c.
def localCycle00197 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4]
    constant := ![-2, -1, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 4 0, .triangle 3 0, .triangle 17 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2]

-- Cycle fingerprint d3f0964187954b02495042735b875d90e16e2e84c2b5df17ce5ab06f527eb54c.
def localCycle00198 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 6, .distance 3 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, 0, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 4 0, .triangle 21 1, .triangle 33 1, .corridorLower 5 6]

-- Cycle fingerprint d40432b1458ea4d7e3572deccd3df4a10f31bd3a3e87b7035ceee0d1b59acd74.
def localCycle00199 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 4, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3, .distance 2 3, .distance 1 3]
    constant := ![-3, -1, -1, 0, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 5, .triangle 2 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 15 2]

-- Cycle fingerprint d43cc45123410eaa58860bb26c628f736bc235932660bbef9163b171ef757c07.
def localCycle00200 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![-2, 0, 0, -1, 0, 3, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0]

-- Cycle fingerprint d50ac029289570a84594ceabd4c8d60beb08e69a9c4c0dbd49ddbf16e1c3b2e1.
def localCycle00201 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, 0, -2, 0, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, true, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 0]

-- Cycle fingerprint d5cdc6cd9ee9ca50c9779a92d6f767ba78f4699647caf9e650673dfc8f00fe16.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, 0, -1, 0, 3, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true, true, false, false] }
  origin := ![.triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint d6139e78f61c10f97de7c6583fc9e9e12bb41611f2a98a61463ca324eca241b7.
def localCycle00203 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.triangle 8 0, .triangle 30 1, .triangle 17 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 2 0, .gapLower 0 3]

-- Cycle fingerprint d621402f41a7f0bb4a0843a2d59144628f98e3f9de6fbb57414cffa439205841.
def localCycle00204 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![0, -1, -1, -1, 2, 0, 0, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 0 2, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .triangle 23 2, .gapLower 1 3]

-- Cycle fingerprint d6caa96722967031ffe73f9e35726796c227e31f3f59d704e11b3a9f9e680003.
def localCycle00205 : Cycle where
  length := 12
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true, true, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint d6cb27ea3ba4c7c6c41b7718249550edd7f26646050c97cfd05010ad2a7788d5.
def localCycle00206 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 2 5, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, -1, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 30 1, .triangle 17 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint d721e909f6ff1906ddda7e4c849036088b7ac3e3ffc8d2a8fc6960ee8ba6edf1.
def localCycle00207 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![0, -1, -1, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .triangle 7 0, .triangle 17 0, .gapLower 1 0, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint d79b942f8959cb95b076756307b03cbb8615c853e502b3c1b677699801529123.
def localCycle00208 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 24 0, .triangle 20 1, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint d9990f8f5d3a72101b3b5d38107c9be4b7285dfc4ba4098dae560360ebac5230.
def localCycle00209 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 2 4, .distance 1 4, .distance 0 1, .distance 1 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, true, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 16 2, .triangle 2 0, .triangle 3 0, .triangle 17 1, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint dd64e9fed20ef91c51b6a2f58a9ac533df3ba0b6f3e9aadfbc11afa26cc26421.
def localCycle00210 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 2 3, .distance 2 6, .distance 1 6, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![4, -1, 0, 0, -3, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 3 6, .triangle 26 0, .triangle 27 2, .triangle 18 2, .gapLower 1 3, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint ddda2d9beffec58ee452cc4d7ad148772d40a7f9e585c6fdacdee3e09e9787b8.
def localCycle00211 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, 0, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0]

-- Cycle fingerprint de36540036feb0e40f294d4562e694eb397b950b5877e5f951f1bbbe3c900481.
def localCycle00212 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, 0, 0, -1, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 15 2, .triangle 1 0, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint de8a2ccd20913236f01a42b4b1b695ffa2d0fe7efa00972a80e2c87d9470bd3b.
def localCycle00213 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![0, 0, 0, 3, 0, 0, -2, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, true, false, false, false, true, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .gapLower 1 2, .triangle 17 1, .gapLower 1 0]

-- Cycle fingerprint dec5ba9da250dc93b2fe5622959aa6572d7d965409c89b0e62aeb48104dd89a2.
def localCycle00214 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 1 5]
    constant := ![0, -2, 0, 0, 3, 0, 0, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true, false, false] }
  origin := ![.triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 2, .gapLower 1 3, .triangle 3 0]

-- Cycle fingerprint df7b598c54458af9c87079593cfe1b4910ba8c82d09305524dc1c9c4b2fc585d.
def localCycle00215 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 4 6, .distance 0 4, .distance 0 1, .distance 1 2, .distance 2 5, .distance 3 5, .theta 3]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .triangle 23 0, .triangle 13 0, .triangle 2 1, .triangle 0 0, .triangle 17 0, .triangle 26 1, .corridorLower 3 5]

-- Cycle fingerprint e3271965c38393f0ca57c425ea828eb78175c906fbacd67ac12c9e74af66ae25.
def localCycle00216 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 4, .theta 1, .distance 1 5, .distance 1 6, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 4, .gapLower 1 6, .gapLower 1 5, .triangle 4 0]

-- Cycle fingerprint e4ed9f7ea4611e915cf3668cfbc9b76f289ee1c09745f7c50672887fb14c58d4.
def localCycle00217 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 1 3, .distance 0 1, .distance 1 5, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 21 0, .triangle 1 0, .triangle 3 0, .triangle 20 1, .corridorLower 3 5]

-- Cycle fingerprint e622f1f62fc992dcf62b64ad2d8567d8d7957751ecdc054f2a41c930a6fb2151.
def localCycle00218 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 0 6, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .triangle 4 2, .triangle 8 1, .triangle 7 0, .triangle 17 0, .gapLower 1 0]

-- Cycle fingerprint e6d0137c9f43949f44a9e08c5d7d124f8b789618c3cdef5baf3e6ee402c302ff.
def localCycle00219 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .distance 1 5, .distance 1 3]
    constant := ![-1, -1, 0, -1, 2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint e6ee6c727c26df3df9fee90ca4cc78ee0a94afa2ec7a99016357d665d162dc65.
def localCycle00220 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, 0, -2, -1, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 21 1, .gapLower 1 3, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint e757a57464c8d0361908a950ea6e96f44e28068d99cb503082ff9cf9715baaf9.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 15 2, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint e77bd302597e42930b5652e5f0ab409ad2e4cde579ecb195bee5dddd5092e5e0.
def localCycle00222 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 1 3, .distance 0 1, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 1 0, .gapLower 1 3, .corridorLower 1 6]

-- Cycle fingerprint e7a6403912147428225acfccd77d8bad3073df1f50415f26515cd1e6a43c9293.
def localCycle00223 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, -1, 0, -1, -1, 0, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 4, .triangle 1 0, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint ea45b561c2189dcb44b3f4daab7018e22d972f070bac7b52cfbbe577f72dfc82.
def localCycle00224 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 1, .distance 1 5, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1]
    constant := ![-2, -1, 4, -2, -1]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .gapLower 1 5, .triangle 2 0]

-- Cycle fingerprint ece4d3753ddf652429c73cf6e6acf2d072e970ea7633fbe61bbe68b40ec15d9b.
def localCycle00225 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 1 2]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 17 0]

-- Cycle fingerprint f1643d5d4dc9af2f579444272d4a89e3ee02e3413e76c88a785911301ffaf6a3.
def localCycle00226 : Cycle where
  length := 6
  data := {
    node := ![.theta 3, .distance 2 3, .distance 0 2, .distance 2 5, .distance 5 6, .distance 3 5, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 5 0, .triangle 7 0, .triangle 30 0, .triangle 33 0, .corridorLower 3 5]

-- Cycle fingerprint f201874d77ccff90bc54c53abaaa95da27c4d34211fc000295bdb921ba6edf97.
def localCycle00227 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 1 3, .distance 1 4, .distance 0 1, .distance 1 6]
    constant := ![-2, -2, -1, 4, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 19 2, .triangle 2 0, .triangle 4 0]

-- Cycle fingerprint f2f27c2c9ae35ebbd8baf72f5e50b7be33bb9a25aa47388b55f14472adf31a6b.
def localCycle00228 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 3 5, .theta 3, .distance 2 3, .distance 0 2, .distance 2 6, .distance 1 6]
    constant := ![-3, 0, -1, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .triangle 20 1, .corridorLower 3 5, .corridorUpper 2 3, .triangle 5 0, .triangle 8 0, .triangle 18 2]

-- Cycle fingerprint f31aea87dbc69ac942ded9f899fd11f1d8f9372db217f47573c4294d3b40c2ac.
def localCycle00229 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 4, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-1, -1, 0, 0, 4, 0, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, true, false, false] }
  origin := ![.triangle 1 0, .triangle 2 0, .triangle 19 1, .gapLower 4 0, .gapLower 4 6, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .gapLower 1 4]

-- Cycle fingerprint f5101c339b6ad55813c0f0b46067ae0fd420007669c5014ab577e30847ee3240.
def localCycle00230 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 1 5, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, 0, 0, -2, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 17 2, .gapLower 1 5, .triangle 4 0, .gapLower 1 2, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint f610889fcafbdf5d355da6e48276c6ba6269078d56dbde5b64704d91d5c3e42e.
def localCycle00231 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, 0, -1, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f66ad2c9f6cfd2acf8d4fad989989997d9c41ab23b0308751aff3134efa84bfa.
def localCycle00232 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 5, .distance 1 3, .distance 0 1, .distance 1 4, .distance 3 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 33 1, .triangle 20 0, .triangle 1 0, .triangle 2 0, .triangle 19 1, .corridorLower 3 4]

-- Cycle fingerprint f7469ec6c6adf0951d2282f7970db332bb378c3ecdc4cdd2258b6be018e030ad.
def localCycle00233 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 1 6, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 21 2, .triangle 4 0, .triangle 2 0, .triangle 16 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint f74bb71f8b77b2e7ee6730537fe6d09faf791847f859acd2b7e646afa7f13ef4.
def localCycle00234 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 1 3, .distance 0 1]
    constant := ![-1, -2, -2, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 2 0, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 20 0, .triangle 1 0]

-- Cycle fingerprint f8ab087f9bc420f50ebf153d0f8329e778924deece726eb201f96f0454ff1f20.
def localCycle00235 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2, .theta 1, .distance 1 3, .distance 0 1]
    constant := ![0, -1, -1, -1, 1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.gapLower 0 2, .triangle 7 0, .triangle 17 0, .corridorLower 1 2, .gapLower 1 6, .triangle 1 0]

-- Cycle fingerprint fad8183223f9c23b2cd467c2f78f9ddd9c9285915cd040e5efdea2c089fecad4.
def localCycle00236 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 3 5, .distance 4 5, .theta 4, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1]
    constant := ![-1, 0, 0, -1, 0, 3, 0, 0, -2, -2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, true, true, false, false] }
  origin := ![.triangle 3 0, .triangle 20 1, .triangle 31 1, .corridorLower 4 5, .thetaNext 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint fb1f8372d92832aceac1f9d38eb4b1192d104b1a2e5af39c69fe8e02b45dff9b.
def localCycle00237 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, 0, -3, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .gapLower 0 2, .triangle 7 0, .triangle 17 0]

-- Cycle fingerprint fcce391cba7700604a2ba2fad562f9acff69d0b17b34e679fa80259382fdf0e9.
def localCycle00238 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 1 3, .distance 1 4, .distance 1 6, .distance 0 1, .distance 0 2, .distance 2 5, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, 0, -2, -1, 0, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 15 2, .triangle 19 2, .gapLower 1 4, .triangle 4 0, .gapLower 0 2, .gapLower 2 2, .triangle 17 0]

-- Cycle fingerprint fe493d098a6ca42ec025c6cee27ed4eb7531a97b8b45b1bd409483e7a4b87102.
def localCycle00239 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 6 0, .triangle 7 0, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint ff8db9b7608dfd9d49cd0753e55a3de850eb7ebc410ad32da781998916423fbb.
def localCycle00240 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 6, .distance 0 3, .distance 0 1, .distance 1 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 2, .triangle 11 0, .triangle 1 1, .triangle 2 0, .triangle 16 1, .corridorLower 1 2, .thetaLower 1]

def library : Library := fun id => if id < 120 then (if id < 60 then (if id < 30 then (if id < 15 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 11 then (if id < 9 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id = 8 then some localCycle00008 else none)) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))) else (if id < 13 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id = 12 then some localCycle00012 else none)) else (if id < 14 then (if id = 13 then some localCycle00013 else none) else (if id = 14 then some localCycle00014 else none))))) else (if id < 22 then (if id < 18 then (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id < 17 then (if id = 16 then some localCycle00016 else none) else (if id = 17 then some localCycle00017 else none))) else (if id < 20 then (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none)) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id = 21 then some localCycle00021 else none)))) else (if id < 26 then (if id < 24 then (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none)) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))) else (if id < 28 then (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)) else (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id = 29 then some localCycle00029 else none)))))) else (if id < 45 then (if id < 37 then (if id < 33 then (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none))) else (if id < 35 then (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)) else (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id = 36 then some localCycle00036 else none)))) else (if id < 41 then (if id < 39 then (if id < 38 then (if id = 37 then some localCycle00037 else none) else (if id = 38 then some localCycle00038 else none)) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none))) else (if id < 43 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id = 42 then some localCycle00042 else none)) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))))) else (if id < 52 then (if id < 48 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id < 47 then (if id = 46 then some localCycle00046 else none) else (if id = 47 then some localCycle00047 else none))) else (if id < 50 then (if id < 49 then (if id = 48 then some localCycle00048 else none) else (if id = 49 then some localCycle00049 else none)) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)))) else (if id < 56 then (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))) else (if id < 58 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none)) else (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id = 59 then some localCycle00059 else none))))))) else (if id < 90 then (if id < 75 then (if id < 67 then (if id < 63 then (if id < 61 then (if id = 60 then some localCycle00060 else none) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none))) else (if id < 65 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id = 64 then some localCycle00064 else none)) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none)))) else (if id < 71 then (if id < 69 then (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id = 68 then some localCycle00068 else none)) else (if id < 70 then (if id = 69 then some localCycle00069 else none) else (if id = 70 then some localCycle00070 else none))) else (if id < 73 then (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none)) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none))))) else (if id < 82 then (if id < 78 then (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id = 77 then some localCycle00077 else none))) else (if id < 80 then (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none)) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)))) else (if id < 86 then (if id < 84 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)) else (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id = 85 then some localCycle00085 else none))) else (if id < 88 then (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)) else (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id = 89 then some localCycle00089 else none)))))) else (if id < 105 then (if id < 97 then (if id < 93 then (if id < 91 then (if id = 90 then some localCycle00090 else none) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id = 92 then some localCycle00092 else none))) else (if id < 95 then (if id < 94 then (if id = 93 then some localCycle00093 else none) else (if id = 94 then some localCycle00094 else none)) else (if id < 96 then (if id = 95 then some localCycle00095 else none) else (if id = 96 then some localCycle00096 else none)))) else (if id < 101 then (if id < 99 then (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))))) else (if id < 112 then (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 110 then (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id = 109 then some localCycle00109 else none)) else (if id < 111 then (if id = 110 then some localCycle00110 else none) else (if id = 111 then some localCycle00111 else none)))) else (if id < 116 then (if id < 114 then (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none)) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))))))) else (if id < 180 then (if id < 150 then (if id < 135 then (if id < 127 then (if id < 123 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none)))) else (if id < 131 then (if id < 129 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none)) else (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id = 130 then some localCycle00130 else none))) else (if id < 133 then (if id < 132 then (if id = 131 then some localCycle00131 else none) else (if id = 132 then some localCycle00132 else none)) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none))))) else (if id < 142 then (if id < 138 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))) else (if id < 140 then (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id = 139 then some localCycle00139 else none)) else (if id < 141 then (if id = 140 then some localCycle00140 else none) else (if id = 141 then some localCycle00141 else none)))) else (if id < 146 then (if id < 144 then (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none)) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none))) else (if id < 148 then (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none)))))) else (if id < 165 then (if id < 157 then (if id < 153 then (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))) else (if id < 155 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none)) else (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id = 156 then some localCycle00156 else none)))) else (if id < 161 then (if id < 159 then (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)) else (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id = 160 then some localCycle00160 else none))) else (if id < 163 then (if id < 162 then (if id = 161 then some localCycle00161 else none) else (if id = 162 then some localCycle00162 else none)) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none))))) else (if id < 172 then (if id < 168 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))) else (if id < 170 then (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none)) else (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id = 171 then some localCycle00171 else none)))) else (if id < 176 then (if id < 174 then (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none)) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id = 175 then some localCycle00175 else none))) else (if id < 178 then (if id < 177 then (if id = 176 then some localCycle00176 else none) else (if id = 177 then some localCycle00177 else none)) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))))))) else (if id < 210 then (if id < 195 then (if id < 187 then (if id < 183 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none))) else (if id < 185 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id = 184 then some localCycle00184 else none)) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none)))) else (if id < 191 then (if id < 189 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none))) else (if id < 193 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id = 192 then some localCycle00192 else none)) else (if id < 194 then (if id = 193 then some localCycle00193 else none) else (if id = 194 then some localCycle00194 else none))))) else (if id < 202 then (if id < 198 then (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none))) else (if id < 200 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none)) else (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id = 201 then some localCycle00201 else none)))) else (if id < 206 then (if id < 204 then (if id < 203 then (if id = 202 then some localCycle00202 else none) else (if id = 203 then some localCycle00203 else none)) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none))) else (if id < 208 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none)) else (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)))))) else (if id < 225 then (if id < 217 then (if id < 213 then (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id < 212 then (if id = 211 then some localCycle00211 else none) else (if id = 212 then some localCycle00212 else none))) else (if id < 215 then (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none)) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)))) else (if id < 221 then (if id < 219 then (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none))) else (if id < 223 then (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none)) else (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none))))) else (if id < 233 then (if id < 229 then (if id < 227 then (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none)) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id = 228 then some localCycle00228 else none))) else (if id < 231 then (if id < 230 then (if id = 229 then some localCycle00229 else none) else (if id = 230 then some localCycle00230 else none)) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none)))) else (if id < 237 then (if id < 235 then (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id = 234 then some localCycle00234 else none)) else (if id < 236 then (if id = 235 then some localCycle00235 else none) else (if id = 236 then some localCycle00236 else none))) else (if id < 239 then (if id < 238 then (if id = 237 then some localCycle00237 else none) else (if id = 238 then some localCycle00238 else none)) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 5, 1, 4, 6, 3], ![2, 5, 0, 4, 6, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 0, 2, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 78 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13696)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 5, 1, 4, 6, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 1, 0, 2, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 53 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13697)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 5, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 0, 2, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 98 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13698)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 5, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 0, 1, 2, 5]], proof := .low (![48, 148, 61, 111, 41, 199, 32, 189, 169, 214, 213, 162, 94, 10, 25, 131, 34, 20, 202, 200, 224, 87, 236, 117, 12, 39, 197, 42]) }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13699)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 5, 1, 4, 3, 6], ![2, 5, 0, 4, 3, 6], ![1, 0, 6, 5, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 0, 6, 2], ![0, 1, 3, 4, 5, 2]], proof := .tail 205 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13700)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 5, 1, 4, 3, 6], ![2, 5, 0, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 0, 6, 2], ![0, 3, 1, 4, 5, 2]], proof := .tail 100 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13701)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 5, 1, 4, 3, 6], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 1, 0, 6, 2], ![0, 3, 4, 1, 5, 2]], proof := .tail 29 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13702)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 5, 1, 4, 6, 3], ![2, 5, 0, 4, 6, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 0, 6, 2], ![3, 0, 1, 4, 5, 2]], proof := .tail 100 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13703)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 5, 1, 4, 6, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 1, 0, 6, 2], ![3, 0, 4, 1, 5, 2]], proof := .tail 95 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13704)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 5, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 0, 6, 2], ![3, 4, 0, 1, 5, 2]], proof := .tail 29 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13705)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 5, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 0, 1, 5, 2]], proof := .tail 119 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13706)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 5, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 0, 2, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 193 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13707)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 5, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 0, 6, 2], ![3, 4, 1, 0, 5, 2]], proof := .tail 193 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13708)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 6, 0, 2], ![3, 4, 1, 5, 0, 2]], proof := .tail 158 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13709)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![3, 4, 5, 1, 0, 2]], proof := .tail 177 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13710)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 6, 0, 2], ![3, 4, 1, 5, 2, 0]], proof := .tail 195 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13711)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![3, 4, 5, 1, 2, 0]], proof := .tail 177 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13712)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![3, 4, 5, 2, 1, 0]], proof := .tail 22 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13713)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 5, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 5, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .low (![164, 63, 121, 128, 35, 144, 88, 129, 115, 68, 74, 168, 143, 130, 19, 174, 71, 27, 7, 62, 69, 181, 139, 102, 222, 194, 46, 185]) }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13714)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 5, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .low (![164, 63, 121, 128, 35, 144, 88, 129, 115, 68, 74, 168, 143, 130, 19, 174, 71, 27, 7, 62, 69, 181, 139, 102, 222, 194, 46, 185]) }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13715)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 15 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13716)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 177 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13717)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 132 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13718)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 6, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 0, 6, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 75 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13719)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 2, 0]], proof := .tail 161 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13720)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 2, 0]], proof := .tail 177 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13721)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 2, 0]], proof := .tail 132 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13722)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 2, 0]], proof := .tail 75 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13723)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 2, 1, 0]], proof := .tail 65 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13724)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 2, 1, 0]], proof := .tail 123 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13725)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![6, 2, 5, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 0, 5, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 2, 1, 0]], proof := .tail 209 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13726)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 4, 3, 6], ![1, 5, 0, 4, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 0, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 82 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13727)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 4, 3, 6], ![1, 5, 0, 4, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 217 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13728)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 4, 3, 6], ![1, 5, 0, 6, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 2, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 133 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13729)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 4, 6, 3], ![1, 5, 0, 4, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 93 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13730)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 4, 6, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 2, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 23 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13731)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 1, 2, 0, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 186 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13732)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![2, 5, 0, 4, 6, 3], ![1, 5, 0, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 1, 2, 0, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 176 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13733)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![2, 5, 0, 4, 6, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 1, 2, 0, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 23 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13734)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 1, 2, 0, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 188 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13735)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![5, 2, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 98 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13736)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![5, 2, 1, 6, 4, 3], ![2, 5, 0, 6, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 0, 1, 2, 5]], proof := .low (![225, 101, 61, 153, 237, 199, 235, 178, 90, 167, 238, 187, 207, 10, 31, 122, 34, 20, 202, 200, 224, 87, 196, 24, 204, 73, 64, 163]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13737)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![5, 2, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 193 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13738)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![3, 4, 1, 2, 0, 5]], proof := .tail 151 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13739)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 2, 6, 0], ![3, 4, 1, 2, 5, 0]], proof := .tail 77 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13740)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 1, 6, 2, 0], ![3, 4, 1, 5, 2, 0]], proof := .tail 226 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13741)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 1, 2, 0], ![3, 4, 5, 1, 2, 0]], proof := .tail 138 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13742)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 1, 2, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 152 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13743)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![5, 2, 6, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 0, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .low (![191, 101, 121, 128, 179, 144, 52, 212, 83, 83, 201, 171, 218, 130, 19, 40, 71, 27, 7, 62, 69, 181, 139, 102, 222, 45, 49, 184]) }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13744)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 2, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .low (![136, 101, 228, 128, 30, 144, 173, 135, 206, 206, 182, 59, 56, 227, 19, 114, 71, 27, 7, 4, 69, 181, 139, 102, 222, 6, 33, 203]) }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13745)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 5, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 2, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 15 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13746)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 5, 6, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 1, 6, 2, 0], ![4, 3, 1, 5, 2, 0]], proof := .tail 226 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13747)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 1, 2, 0]], proof := .tail 138 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13748)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 1, 2, 0]], proof := .tail 50 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13749)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![2, 6, 5, 0, 4, 3], ![1, 6, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 1, 2, 0]], proof := .tail 112 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13750)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 1, 2, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 152 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13751)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 1, 2, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 17 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13752)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 2, 5, 0, 4, 3], ![6, 1, 5, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 1, 2, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 239 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13753)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 4, 3, 6], ![5, 1, 0, 4, 3, 6], ![5, 4, 0, 1, 2, 6], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 16 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13754)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 4, 3, 6], ![5, 1, 0, 4, 6, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 96 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13755)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 4, 3, 6], ![5, 1, 0, 6, 4, 3], ![5, 4, 0, 1, 6, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 2, 1, 0, 6], ![0, 1, 3, 4, 2, 5]], proof := .tail 175 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13756)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 4, 6, 3], ![5, 1, 0, 4, 6, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![0, 3, 1, 2, 4, 5]], proof := .tail 126 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13757)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 4, 6, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 2, 1, 0, 6], ![0, 3, 1, 4, 2, 5]], proof := .tail 80 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13758)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![5, 2, 1, 4, 3, 6], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 0, 6, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 2, 1, 0, 6], ![0, 3, 4, 1, 2, 5]], proof := .tail 126 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13759)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![5, 2, 0, 4, 6, 3], ![5, 1, 0, 4, 6, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 2, 6], ![4, 3, 2, 1, 0, 6], ![3, 0, 1, 2, 4, 5]], proof := .tail 154 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13760)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![5, 2, 0, 4, 6, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 1, 6, 2], ![4, 3, 2, 1, 0, 6], ![3, 0, 1, 4, 2, 5]], proof := .tail 80 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13761)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![5, 2, 1, 4, 6, 3], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 0, 6, 1, 2], ![4, 3, 2, 1, 0, 6], ![3, 0, 4, 1, 2, 5]], proof := .tail 215 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13762)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![5, 2, 1, 6, 4, 3], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 0, 1, 2, 5]], proof := .tail 126 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13763)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![5, 2, 1, 6, 4, 3], ![5, 2, 0, 6, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 0, 1, 2, 5]], proof := .tail 126 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13764)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![5, 2, 6, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 1, 0, 2, 5]], proof := .tail 193 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13765)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 1, 2, 0, 5]], proof := .tail 151 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13766)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![5, 6, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![3, 4, 2, 1, 0, 5]], proof := .tail 160 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13767)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 6, 0], ![3, 4, 1, 2, 5, 0]], proof := .tail 77 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13768)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![5, 6, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 1, 6, 0], ![3, 4, 2, 1, 5, 0]], proof := .tail 81 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13769)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 2, 6, 1, 0], ![3, 4, 2, 5, 1, 0]], proof := .tail 177 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13770)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![5, 4, 6, 0, 1, 2], ![5, 3, 6, 0, 1, 2], ![4, 3, 6, 2, 1, 0], ![3, 4, 5, 2, 1, 0]], proof := .tail 145 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13771)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 2, 6, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 0, 6, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 0, 2, 5]], proof := .tail 76 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13772)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 1, 2, 0, 5]], proof := .tail 3 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13773)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![5, 2, 6, 0, 4, 3], ![5, 1, 6, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 6, 0], ![4, 3, 1, 2, 5, 0]], proof := .tail 142 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13774)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 6, 2, 1, 4, 3], ![5, 6, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 110 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13775)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![5, 6, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 15 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13776)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![5, 6, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 177 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13777)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![5, 6, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 145 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13778)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![5, 6, 3, 0, 1, 2], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 18 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13779)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 5, 2, 1, 4, 3], ![6, 5, 2, 0, 4, 3], ![6, 5, 1, 0, 4, 3], ![6, 5, 4, 0, 1, 2], ![6, 5, 3, 0, 1, 2], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 99 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13780)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 1, 0, 2, 5, 6], ![0, 1, 2, 3, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 221 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13781)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 0, 1, 2, 5, 6], ![3, 1, 0, 2, 6, 5], ![0, 1, 2, 3, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 156 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13782)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 3, 5, 6], ![4, 0, 1, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![0, 1, 2, 6, 3, 4], ![0, 1, 2, 5, 3, 4]], proof := .tail 8 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13783)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 2, 3, 4]], proof := .tail 208 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13784)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 2, 3, 4]], proof := .low (![134, 86, 85, 54, 157, 97, 37, 234, 55, 190, 155, 211, 118, 84, 13, 92, 108, 36, 66, 89, 216, 9, 47, 220, 14, 229, 51, 60]) }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13785)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 3, 6, 5], ![4, 0, 1, 2, 6, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 2, 3, 4]], proof := .low (![134, 86, 85, 54, 157, 2, 37, 234, 55, 190, 155, 230, 118, 84, 13, 92, 108, 36, 66, 89, 216, 9, 47, 220, 14, 229, 51, 60]) }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13786)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 223 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13787)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 1 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13788)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 1 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13789)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 1, 0, 2, 6, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 165 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13790)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 44 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13791)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 1, 2, 4]], proof := .low (![233, 231, 180, 210, 103, 147, 0, 140, 141, 38, 105, 79, 118, 28, 124, 57, 58, 36, 43, 120, 170, 9, 72, 5, 150, 127, 70, 219]) }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13792)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![0, 1, 6, 2, 3, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 26 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13793)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 137 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13794)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 1, 0, 6, 2, 5], ![0, 6, 1, 2, 3, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 67 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13795)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 1, 6, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 1, 3, 4, 2]], proof := .tail 137 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13796)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 0, 6, 1, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 0, 3, 1, 4, 2]], proof := .tail 240 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13797)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 0, 1, 4, 2]], proof := .tail 149 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13798)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 4, 6, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 4, 6, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 2, 4]], proof := .tail 198 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13799)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 4, 6, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 0, 6, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 0, 4, 2]], proof := .tail 198 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13800)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 0, 2]], proof := .tail 91 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13801)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 0, 6, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 0, 2]], proof := .tail 106 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13802)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 6, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 0, 6, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 116 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13803)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 4, 6, 0, 3, 5], ![1, 6, 0, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 1, 6, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 1, 4, 2, 0]], proof := .tail 183 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13804)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 0, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 1, 2, 0]], proof := .tail 106 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13805)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![2, 6, 4, 0, 3, 5], ![1, 6, 0, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 116 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13806)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 0, 4, 3, 5], ![4, 6, 0, 1, 2, 5], ![3, 6, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 3, 4, 2, 1, 0]], proof := .tail 146 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13807)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![6, 2, 4, 1, 3, 5], ![6, 2, 4, 0, 3, 5], ![6, 1, 0, 4, 3, 5], ![6, 4, 0, 1, 2, 5], ![6, 3, 1, 0, 2, 5], ![6, 0, 1, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 166 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13808)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 1, 0, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 2, 3, 4, 5]], proof := .tail 172 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13809)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 5, 3, 6], ![4, 0, 1, 5, 2, 6], ![3, 1, 0, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 2, 3, 5, 4]], proof := .tail 107 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13810)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 5, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 2, 5, 6], ![0, 1, 3, 2, 4, 6], ![0, 1, 3, 2, 4, 5]], proof := .tail 232 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13811)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 5, 6, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 2, 6, 5], ![0, 1, 3, 2, 6, 4], ![0, 1, 3, 2, 5, 4]], proof := .tail 104 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13812)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 6, 5, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 2, 6, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 2, 4]], proof := .tail 192 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13813)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 4, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 2, 4]], proof := .tail 11 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13814)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 2, 4]], proof := .tail 159 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13815)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 3, 6, 5], ![1, 0, 4, 6, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 1, 3, 2, 4]], proof := .tail 159 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13816)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 0, 2, 6, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 2, 4]], proof := .tail 21 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13817)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 4, 1, 3, 6, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 0, 3, 1, 2, 4]], proof := .tail 113 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13818)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 4, 1, 6, 3, 5], ![2, 4, 0, 6, 3, 5], ![1, 0, 4, 6, 5, 3], ![4, 6, 0, 1, 5, 2], ![3, 1, 0, 2, 6, 5], ![6, 0, 1, 3, 2, 4], ![5, 3, 0, 1, 2, 4]], proof := .tail 125 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13819)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 6, 4, 5, 3], ![4, 0, 1, 5, 6, 2], ![3, 1, 0, 6, 2, 5], ![0, 1, 3, 6, 2, 4], ![0, 1, 3, 5, 4, 2]], proof := .tail 109 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13820)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 5, 6], ![1, 0, 6, 4, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![0, 1, 6, 3, 2, 4], ![0, 1, 5, 3, 4, 2]], proof := .tail 11 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13821)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 3, 6, 5], ![1, 0, 6, 4, 5, 3], ![4, 0, 1, 6, 5, 2], ![3, 1, 0, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 1, 3, 4, 2]], proof := .tail 137 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13822)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 4, 1, 3, 5, 6], ![2, 4, 0, 6, 3, 5], ![1, 0, 6, 4, 5, 3], ![4, 0, 6, 1, 5, 2], ![3, 1, 0, 6, 2, 5], ![0, 6, 1, 3, 2, 4], ![0, 5, 3, 1, 4, 2]], proof := .tail 21 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 13823)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (13696 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 13696 ≤ id.val) (hhigh : id.val < 13824) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 13696)) = true := by
  let j : Fin 128 := ⟨id.val - 13696, by omega⟩
  have hsum : 13696 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (13696 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard107
