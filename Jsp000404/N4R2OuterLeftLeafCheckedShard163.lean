import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard163
open N4R2OuterLeftReplay

-- Cycle fingerprint 0043b988629118d2fdd7bc5cffb169376fcfece2c5bce2c8375a56ac02fd765c.
def localCycle00000 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -1, 0, -1, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 5, .triangle 16 1, .triangle 17 0, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6]

-- Cycle fingerprint 00d87c056eb2dd22f4de24ddde71fd06ccd66e39cfb0313a82ed536bbab246b9.
def localCycle00001 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 023e3adbe0a5716e9a29e5b6468b42f7f9f051a03d7359dc73b5119348a26270.
def localCycle00002 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 0310ff91b2389153a1c2728f6df594b74a2179188755e0388c2847cc91b9632b.
def localCycle00003 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 07231ae61fb6d95e71406d41130954f16466c8279a8c59479941ebee6fa88227.
def localCycle00004 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-1, -1, -2, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 8 0, .triangle 18 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 07a978c3c9c6183724e92af296a2ea282f69eb273b55865f202306c04c1e2a54.
def localCycle00005 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint 07b13ce310877dd96c2ded4ab924d4fcb312c2d368ab33d7eb2110be6d9210ae.
def localCycle00006 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 07b7780effb8ad959f03c9680d517ed863466d06bb21ded48c955571e31232b3.
def localCycle00007 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 6]
    constant := ![0, -1, -1, -1, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.triangle 11 1, .triangle 10 0, .triangle 20 0, .corridorLower 1 3, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 8 2]

-- Cycle fingerprint 0cd2e71b44ecb517211f7bda5bf5d4e20ff90615c8132a187837c2c92d9d5b00.
def localCycle00008 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6]
    constant := ![0, -2, -2, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2]

-- Cycle fingerprint 109d4effc582e65ecede305f2e8dd81474b2392fc1fc0c3964a2ffc78058d336.
def localCycle00009 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 6 1, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 12fd0a5d491de1584d21af489bfa36527a0b3590155d7dcc94d8f8f0b204c7c3.
def localCycle00010 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 4 0, .triangle 23 1, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 130d819f68d7765bafc3185663580fe55e294da9aa24a9d74534a49213ab8be6.
def localCycle00011 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 2 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 13eaee517f82b6c2b1cf42bba5a6263300d5a0ab479406c5023e0e06d316714e.
def localCycle00012 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4]
    constant := ![3, -1, -1, 0, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 20 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 1506b1eb2c9e9a94ccbce10b039ddfe5c6fbd8576fe584eb32c91151e3808097.
def localCycle00013 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-1, 0, -1, -1, 2, -2, -1, -1, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 157b1a5895366f697fda7170e558bc50be1e1a691f54bb421ee48e9ff354c477.
def localCycle00014 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -1, 0, 0, -2, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 15f2a6b4c914162526d2ad604df46679a4b816f100bf064bd50e4e21082c7fcb.
def localCycle00015 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 195be1b48aa6290b889b664d65a2459be4f142f6536b3f7ef7e12d0a8923af58.
def localCycle00016 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 5, .corridorUpper 0 1]

-- Cycle fingerprint 1a12a6fefb2f0ae8420c0e305cefcc2f70885d40fc59fef471969e84804cb024.
def localCycle00017 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 5 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 17 2, .triangle 24 0, .triangle 33 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 1a20f5024a96a8c73b273ff43e247ed563a344141ee297421095411896426171.
def localCycle00018 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5, .thetaLower 4]

-- Cycle fingerprint 1baabcfa02ef9d1627c2f91467e47ce15d95cada767045a3c6c8e5fae01d7494.
def localCycle00019 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 23 0, .triangle 16 1, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 1bafde5d6d58e53539062f909fc1517147327579d940c42e5e57c627fe6a6d65.
def localCycle00020 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -1, 0, -1, -2, -2, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false, true, true] }
  origin := ![.triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 1c4cb1bfe3f135919f8292ae9515a64d496a5c9c306d6f44837022869895c958.
def localCycle00021 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 1f805dde4ba33a959704b0ae5d4f112579be0a86d491975ac1e5eea359dbf222.
def localCycle00022 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 2096cc885a79a2d816559503cdd1450d87adf5a7e60fc8d725368a7a19f8e70b.
def localCycle00023 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 21e687e51d47a8fea98092d28825b4b8769d339dd9cf806b2aae5a1af25af490.
def localCycle00024 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 15 0, .triangle 26 0, .triangle 31 1, .gapUpper 4 1, .triangle 16 1]

-- Cycle fingerprint 229a05d011838f168c0b8453bf4a64176b2cd3dc89ec36a447895c515f833ef7.
def localCycle00025 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, 2, 0, 0, 0, -1, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, true, true, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 5 2, .triangle 11 0, .triangle 21 2, .triangle 24 1, .gapLower 1 1]

-- Cycle fingerprint 23296c87f1613e5736ece29e36513eeb69431af9b56fa59e8e7aeac097c7a9d0.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 2]

-- Cycle fingerprint 24a43e81a026cfbec89d33811c4668445641338ee7bb302d4cf2b5d9250daf28.
def localCycle00027 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3]
    constant := ![-2, 3, -2, 0, -1, 0, 0, -1, 3, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false, false, false, false, true, false] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1, .triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 20 0]

-- Cycle fingerprint 255527ed1b79836d493bea8a74748503c5a06439d3206ff8c6cfdf870a9f2bdb.
def localCycle00028 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint 265286f33e94e8d1084daa31fa5ef40991ba6de8e52eaf39d9d82c3f7e0f2190.
def localCycle00029 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, 0, -1, 3, 0, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, false, false] }
  origin := ![.triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 2c97e47b136dc6a49e9833f545b9dfdb9e844b80ca48683598353accc82d82f4.
def localCycle00030 : Cycle where
  length := 14
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 30 1, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 2ccebf4e680cc1d8eefc62718a6f19a212e34cfff52377f7fe0fa099825c6854.
def localCycle00031 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 17 2, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 30c44e4803b45c4b145ada6ed671378e90bbdf9b662f360107aa5873e21c369d.
def localCycle00032 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 16 1, .triangle 18 2, .triangle 24 1, .triangle 20 1, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint 35c556a5b89d3a8ae20058a3bba746e64da62f7c1460a369b68a54f8639c3937.
def localCycle00033 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 29 1, .corridorLower 4 6]

-- Cycle fingerprint 364359bdca56063752587979ae8e8b66baa5f98995b802c3932514482da7a9ab.
def localCycle00034 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 37df33d588f16b1b915530c36a442baa5ec95737831b38a185837706d68a2bdf.
def localCycle00035 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 18 2, .gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint 3b3aa028e9aa7e02b3d926fd8050d2fa9617b5e2d7b8c0a77afa77033594837f.
def localCycle00036 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 2 6, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 29 2, .triangle 8 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint 3bbdd7aca88aaafb44198af332375803236fb65881c510dd64c0ac215ad0e1b3.
def localCycle00037 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 1 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 21 2, .triangle 23 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 3caf2d617859212e924e652fe1fab464c5e01ed75c88adedec1baa818c76c15c.
def localCycle00038 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -1, 0, -1, -2, 0, -2, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 3eb5bc63179596ebd4a2646c8bfbd007a373ffcc84d86b44cde0cf2d3208c951.
def localCycle00039 : Cycle where
  length := 9
  data := {
    node := ![.distance 2 6, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6]
    constant := ![-1, -3, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 18 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0]

-- Cycle fingerprint 3ee4f8e6e26e276a5017a72ada2b76456d5e1ecc6028d9dadb6efb7f70660f0f.
def localCycle00040 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 0 1, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 3f0704bf03ae3ab0932c26e94f57211b2303705769d3406b95f994f06c03af2a.
def localCycle00041 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 40f91ce0777cfbb144690fc41bf05fdac1b118d46a9c8a94e3ff66f5bdc72304.
def localCycle00042 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![-1, -1, 0, -1, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.triangle 9 0, .triangle 11 0, .triangle 33 1, .triangle 20 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint 4229a1f996d6bdd3bb0aac43090dd88808ce5f23bc4ad2081f0139b4d6f06522.
def localCycle00043 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4322ef8e93e27c9ab32e77ed75df75c22cafd7cfa42800134eb37c600fb8c759.
def localCycle00044 : Cycle where
  length := 10
  data := {
    node := ![.theta 2, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -1, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 432fdf0f8d2f8971c6865e353132e19c3af4a8a1350b1efd72bf7bfcd6fbbe46.
def localCycle00045 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3]
    constant := ![-1, 4, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 2 0, .triangle 16 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 44375e4f4f104d8e6069ee562b8660ddfa30a1cdddbe8d00289e5987f7e5f5c8.
def localCycle00046 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 446fb0d6ba70b749e12aa417a5fcf7e2895f8364913f407f70a7a7bbeb44948f.
def localCycle00047 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 4, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 4517249e9f253674337b7d3719515ec85e3f5c61777d197a02c54caa0aaf60a0.
def localCycle00048 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 21 2, .gapLower 1 2, .triangle 17 1, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 454db32997111d1f6ad76e7f7792f819701fd87ccdd7cb6c232c47dd3789dc98.
def localCycle00049 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 30 1, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 467d295298c48180280acb6940f4e19132228438786700977fdc2f0bf86f0ff5.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0]

-- Cycle fingerprint 46e198a72c17c755839ea320793f17eaca030105ea137ec45d3b4f763286a532.
def localCycle00051 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4]

-- Cycle fingerprint 4851659af35cf6d55cb1d8f974a45da20b33a00edc0424f892ecc1f7165f91f2.
def localCycle00052 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-1, 0, -2, 0, -2, -1, 0, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, false, false, true, true, false] }
  origin := ![.triangle 8 0, .triangle 18 2, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 4855dba80057abd9e8f8f888ecb584c205463b12b3700abbb8266e8035dd4d5a.
def localCycle00053 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 48b422755bef84bfeb4bd7c3de8e84172cdca26f9e6f033ca410b4d2908ed666.
def localCycle00054 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 49805fb7e4d2c6519e1041d66a794ec8a50eccc52f9b1dcc3a769469706b4bf1.
def localCycle00055 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 499fc58ec089fa56ea46ad532940f84ff6c7986a80f6523b133f6f3b501fad5d.
def localCycle00056 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, -2, -1, 4, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 17 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 2 0, .triangle 23 2]

-- Cycle fingerprint 4a883d543cb7dc5deb74cfa27cecf0589e788a0704a57fc0ce74f3ca15ca9518.
def localCycle00057 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5]

-- Cycle fingerprint 4b6a54eb25135289bbaf9b812af32f813a00fa1ab8e35eb1b1db68faa4affcfd.
def localCycle00058 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint 4c021d87396de9c01a45ab1374dc7ec1a46e5f70175522d313914d9e98e1a36e.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 4c4d6465ffb2e548bc0ad0695af8358f850a7d516d682b0c2bdbd16a87f9d072.
def localCycle00060 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint 4d31bf3f0feaff42ec694c4445fe794f3a9b447b377cbc23107a3879697ed907.
def localCycle00061 : Cycle where
  length := 13
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, 0, 0, -1, -1, 0, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false, false, true, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1]

-- Cycle fingerprint 4d4c63ce8bc1e6d37d18c383ae9aa44e4474f9e5e2bafa3107cdf008401fca57.
def localCycle00062 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 4e8b787aaf3bae3c17a3f74eb3fa6b1959d6d38f8266648815336bf292366126.
def localCycle00063 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 6, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 23 2, .gapLower 1 3, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 4f4e873cb554b5b86c844f435c846847554c5015cf102267bf18db3d429425b4.
def localCycle00064 : Cycle where
  length := 8
  data := {
    node := ![.theta 2, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint 51b14c48b48dbb846984c5a31ed77dbad6e80a6fad99d7bc728785777f61b82d.
def localCycle00065 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 54a548c01dd81cdf698fe5106df2a8ddeead83f7853cfb1ba4503d116073d5fe.
def localCycle00066 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 1, .gapLower 1 4, .gapUpper 5 1]

-- Cycle fingerprint 55fc17209ed48a3122c04a8cc900d15d425c23d6fe78018740591f2dc654be5a.
def localCycle00067 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4]
    constant := ![0, -1, -1, 3, -3, -1, -1, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 25 1, .triangle 15 0, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0]

-- Cycle fingerprint 57e116fb4946ca29596ca8d61682c97d467cb6469828953cdc947a04a5ff70ad.
def localCycle00068 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint 598293ca09f94b2798cf4db4f6e8b1ab33f327291be3d0dc3e34f5f7481b2273.
def localCycle00069 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 5a28d79874061aa88c97bb8cfb69957fd192b0ba3bcd40830a8ac0da13553ac0.
def localCycle00070 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 5c6e5f4b40087b9e698fde147f434dc3a9a8f44c8333937ecc28c510845d7888.
def localCycle00071 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 5]
    constant := ![0, -2, -1, 0, 0, 3, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 24 0]

-- Cycle fingerprint 5c82a8bceae50980113a94d73f970773cdb7cb82e71eea911a6022bc6eb7d22d.
def localCycle00072 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, -1, -1, 3, -3, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 5cfd2802a412353c70f3656596a31eb8ff3978b96c9046adc33888ce5fae8ca5.
def localCycle00073 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![0, -1, -1, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 7 1, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 5d204faeb79628df0b11d536549349b3323e7b9ac25c1db24333a87b059ee6fc.
def localCycle00074 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 6019e15f1886865fd8a8b8a9327c8887661adf3578a8458cc6daa7f0bd97fb03.
def localCycle00075 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 60da3f933a4a261107f5dd05b8cb64015efbdcb5016e217813172fe8418dd8eb.
def localCycle00076 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0]

-- Cycle fingerprint 6405df57451a5c7215e5f02d526f7845f70df0946466eb64eed6693e9d6369f2.
def localCycle00077 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 64f61d124f6de9e8d0f6a34c12a8af017f0944b03dab5d7e97ac653536a57a60.
def localCycle00078 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-3, 0, 0, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2]

-- Cycle fingerprint 65bec8b0b849f4cb6de43917d55628c0fed6fd0d0b36457efe38fc914f8493a8.
def localCycle00079 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 6 0, .triangle 16 2, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 6766bc97d2e2ff0b74a706039e727a4d111b1f3c57910531c77f922ccece51c3.
def localCycle00080 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 13 0, .triangle 6 1, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 6800bab4a7b050c1d0d0c77679ad6e114834deed2801c4f6963c1fa5fff5795f.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, 0, -1, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 5 2, .triangle 10 0, .triangle 20 0, .gapLower 1 0]

-- Cycle fingerprint 6a31175ed77a2785c5393c8dc3daea9757344548d89b5ea227981f071af3a4d2.
def localCycle00082 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 18 2, .triangle 21 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 0]

-- Cycle fingerprint 6bf6aae237348bdf89a1977ca7d96502e9991c265d7ddcfb764e87b8e8207370.
def localCycle00083 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 27 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 6c5b8d349d319d9150fa7b7c12051c691b058c57b271c1a5215a5bb30f6d0c39.
def localCycle00084 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4]
    constant := ![0, -1, -2, 3, -2, -1, -1, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 25 1, .triangle 15 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0]

-- Cycle fingerprint 6d65f2bf6348f44f0c1f636e7afe6ff31a74c655019c85a4b4f30064ec3d8815.
def localCycle00085 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 6e4bf29f148132e18ca14bf7e2f32cfe89f78dfeeec88ab1323f7ef16a60e616.
def localCycle00086 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 6eb890f5fbbf0cc81d97613b220173bc2f1022c3c6ae76169cb6d79a9d35cb24.
def localCycle00087 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 4, .gapUpper 5 1]

-- Cycle fingerprint 7245ab967423989c0ce613f7fd0b987eac6989bf562a4cffa2bbb170323e2bc3.
def localCycle00088 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![0, -1, -1, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 7 1, .triangle 8 0, .triangle 18 0, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 7259d913abf72cf39e13ef91f091ddc0e73ba3cfbd4c0a36d2bd31fc9ebc02a4.
def localCycle00089 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 72d0f80d1782b683202be2ce1c3e0d49e285fe21e9b3554caa74d47c2cf9e161.
def localCycle00090 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, -1, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 20 0, .gapLower 1 0, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 5 2]

-- Cycle fingerprint 7776fff64628298833319306871b732fd65d54673336fb0cdb29e4260f56eaf2.
def localCycle00091 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint 7b2011fa748549f54ab8630f02abf00b1e2fce5a727b6635e9ff9a19fb0b57c0.
def localCycle00092 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 7b8789f0364b3db5fc76155daf494f079008e17c9e8c49f9295ac2591aa8a1f1.
def localCycle00093 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7bbc51c9407d0b9db9cc1c19d9a9ea0ab0db0f73d8e1176903f33fbc6098e9e7.
def localCycle00094 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5]
    constant := ![-1, -1, 0, 0, -3, 0, -1, 0, 0, 3, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, true, true] }
  origin := ![.triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 23 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2]

-- Cycle fingerprint 7fc1cf3083e29d35e879dbe97cf2d4e54a2ae20a5f41b63af4e1278c59bf8243.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2, .triangle 21 1, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 805ead36e987cee0bd87bc09544fbd2deb77052be86cc8008618b4b9d67512a3.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 2, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, 0, -2, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 17 2, .triangle 20 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2]

-- Cycle fingerprint 8095afb2d6432dd0a995b1aca3c6db25ca0bd52acc5308b5f7257dd766e933e4.
def localCycle00097 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 23 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 812348f99dd3f2b74e0302a7a949a235c553c25107efd6d492402a710e417d1e.
def localCycle00098 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 81427d2c78f03357e25cb8b2c043c7a1e3b435cde1d8656cc1b5fb9f6de8aae7.
def localCycle00099 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 4]

-- Cycle fingerprint 81f664c8cc29b2ceab738cf51648058ed4c8a2c5c842a743cc46d07fb8b7d6b2.
def localCycle00100 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 2 3, .distance 3 6, .distance 4 6, .distance 1 4, .distance 1 2]
    constant := ![-1, -1, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.triangle 15 0, .triangle 27 0, .triangle 32 1, .gapUpper 4 2, .triangle 16 1]

-- Cycle fingerprint 831204af5271dc22d851ccf5c05a8ecaa8c24ca32690da616b280c1e51056e2d.
def localCycle00101 : Cycle where
  length := 17
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, 0, -1, -1, -1, -1, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 2, .triangle 13 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 85a5161914c2d995d83a98a65ba63c1815395d766425b629d79353ea5ea0b9b3.
def localCycle00102 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 85b4190868325e7b091e8c9f6d7d86419c5996d3d32921365ccc2f4516e0aa99.
def localCycle00103 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 86cc956028f3831b365fa024c4a197c47d14b058c5e60d92da2ec3f9d2cf9dc1.
def localCycle00104 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 86f1699d9ad72c43d30580795ad4ebb9186bf9f54c0af26bc2938b5deaca46f3.
def localCycle00105 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-1, 0, -1, -2, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 8 0, .triangle 30 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 8701c6cc9907ad21aec5fe389ee8ec0ddb1dfbef24066f4e3e410a48b0d08c82.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, -2, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 10 0, .triangle 20 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 5 2]

-- Cycle fingerprint 876b495898da0aee2667ebb8d9211a01d6fe1b6488556d6d590a4fcfb4c27ba6.
def localCycle00107 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 884bdf49ce9ab66bcf74876bbbab9155e2b4e534787673ef8f0a9df17e49b300.
def localCycle00108 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 8add9f847c5cdd6c0ef85ae018714e5632aa4cd64ee7651a8b8891415d5c3685.
def localCycle00109 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 3, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 21 0, .triangle 15 1, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 8cdbd5991f8f586b001ccee1d887abded924237b60c50ca3df68ee63e3a418b6.
def localCycle00110 : Cycle where
  length := 13
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6]
    constant := ![-1, 0, -2, 0, -2, 0, 0, 3, 0, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, true, true, false, false, true] }
  origin := ![.triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1]

-- Cycle fingerprint 8e530950249fd7b8c9e3296a14ff730eddda42ca653a4466decc11734e5dc794.
def localCycle00111 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 5, .distance 1 2, .distance 1 5, .distance 2 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 2, .gapLower 1 2, .triangle 17 1]

-- Cycle fingerprint 8f1064f8d3be493460a47f0f18db1b9ab1c84bf58e425666a1a11c542c48089e.
def localCycle00112 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 27 1, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint 910afa13d0101630f16286d7092bb39b9347374c3b538f35a51d4a65ae472692.
def localCycle00113 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .corridorLower 1 2]

-- Cycle fingerprint 932717fdd09166c88d5fac2827481558c9cb08721746f6905b2f346348bc0088.
def localCycle00114 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint 9332ef7296469ec7790ea4df072f051254cf69355a4d41bf96823b848c0f8acb.
def localCycle00115 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 6, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 15 2, .triangle 21 0, .triangle 33 1, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint 93414166f86daeaa195e2342a4abaae1d4da762fe8b0629be8ad4b6c89e39027.
def localCycle00116 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, -2, -1, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 938efa9cd2c4130c5fbac5be372a610ef7d1e3b8f5274141ba466223cf408213.
def localCycle00117 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 959d675b0340691faf080181c741c2238550d1af990515e13d5965e3d329aabe.
def localCycle00118 : Cycle where
  length := 12
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2]
    constant := ![-1, 0, -1, 0, -3, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 8 0, .triangle 30 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0]

-- Cycle fingerprint 99190ef61ee87d7153d71afc6a17bee7c9c536e48b39da5f14d546e19d44ecf1.
def localCycle00119 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 996e74de54e8690d1987a3c29060acc2903341a5aefa2a66a344100038acffcb.
def localCycle00120 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, 0, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .triangle 19 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 99a490321cba31ca3e40cb433867870cabeb37e2fbcceb37773dc91811273341.
def localCycle00121 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4]
    constant := ![0, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, false, false, true, true, false] }
  origin := ![.triangle 16 2, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 6 0]

-- Cycle fingerprint 99b37ee67bbf4b51034f3ce78bd5b70566343dba7e8549bcd252a3101da77c1b.
def localCycle00122 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![1, 0, 0, -1, 0, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2]

-- Cycle fingerprint 99dc4fbb01ee27e194408ebbde72dc5498d53c29614649da6199e89c147a6149.
def localCycle00123 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 27 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 9d042766b4a882e454444ac32f85041bf4aacef7b0cbc0e38180c94a9d34f0d8.
def localCycle00124 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, 0, -1, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 9e5d3f9eb9c9bafc73993f979befc5fd584028548dc55c604550d1c48e1d48a3.
def localCycle00125 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![-2, -2, -1, 4, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 9e5e28380a01ca7ebfaf67145a47da72adcd2ef3db30789065dd0bf25cae40e8.
def localCycle00126 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 2, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 9ea52041d3f66d698e31b4040f66641345a567440cc4163c1c61d2b2ac292eba.
def localCycle00127 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 18 0, .triangle 29 1, .gapUpper 4 2]

-- Cycle fingerprint 9f1b479827a7a9fe159f5fb2898f36fe6cc2f3474826d6a641b6aad411c6870f.
def localCycle00128 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6]
    constant := ![0, -1, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, false] }
  origin := ![.triangle 30 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 0]

-- Cycle fingerprint 9f4eb9ad27805a9ce02d7dcbd765f8e4bad2a26420f5f7203b56ae6c6e02832c.
def localCycle00129 : Cycle where
  length := 16
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 2 6, .distance 0 2, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, -1, 0, -1, 3, 0, 0, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 23 0, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 29 2, .triangle 8 0, .triangle 5 2, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint a21792f0dca1f539525df1510c1412f650c7f1e6337e1f3e1f600ad99729e55c.
def localCycle00130 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 0 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 2 4, .distance 0 2]
    constant := ![0, 2, 0, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true, false] }
  origin := ![.triangle 7 2, .gapUpper 5 5, .triangle 34 2, .triangle 32 0, .triangle 25 2, .triangle 6 0]

-- Cycle fingerprint a2835259b88baad8cfb3da162673c6642bf723ab600071dcff1acfd0ef171e64.
def localCycle00131 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint a2abe624873508abc7e330290ec619263c9014e610653f6b33dcc21a6320615b.
def localCycle00132 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2, .distance 1 5]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 5, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint a492bc8a5735d25398281e7223ae204e8ba039be1c8183a2da5d9440f60a7d5b.
def localCycle00133 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 0, .triangle 9 0, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint a4cc290c73d4fc910464cf00aab7f3f3d17ed36cc48156d14eb20edcc1f9e54e.
def localCycle00134 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 32 0, .triangle 34 1, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint a7b62d31852597d12a31abfd11cd4b233b4d48ff4c177cee971a478c925c093f.
def localCycle00135 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint aa6e203cd6fade9d386387e6f024447dbab7b3628741cee4c9a19a8e8a494d7a.
def localCycle00136 : Cycle where
  length := 9
  data := {
    node := ![.theta 2, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2]
    constant := ![4, -1, 0, -1, 0, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false] }
  origin := ![.gapLower 2 6, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 26 0, .corridorLower 2 3]

-- Cycle fingerprint aab5e6660832c7d8070d0087c27ee8080dce542ff77f20efcd1d982b119b1d5e.
def localCycle00137 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 29 1, .triangle 23 0, .triangle 22 0, .corridorLower 4 5]

-- Cycle fingerprint abaafa94a9c6047f8e670ccafb4893335e1f42681a02c195a361955d41c9562b.
def localCycle00138 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, 4, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 4, .gapLower 1 6, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint ac52088406b17996a5bdb5804ef4a8727316056eec1de7ab4052b6aa4f83a81b.
def localCycle00139 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 3, .distance 1 3, .distance 1 2, .distance 2 3]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 3 1, .gapLower 1 1, .gapUpper 2 1]

-- Cycle fingerprint adedc6d8fc48517d191d5d3fcb54829099a860ccc1fbd5d71388fe749718b65c.
def localCycle00140 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint adf1301a0828ca682ecfab6522233fc74df444851291243e314c3e43eec01cf0.
def localCycle00141 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 1 2, .distance 2 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 16 0, .triangle 15 0, .triangle 26 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint affa4d9afb14d3c47fe3bc89bdf67431e0ac90ebdc74f456f602d8ca38c16787.
def localCycle00142 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, -1, -1, 1, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 20 0, .corridorLower 1 3, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 5 2]

-- Cycle fingerprint b097eb62f69455073f6cfeef59d820d3599ee516486c024c501b0e4a25aa3b50.
def localCycle00143 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, 0, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint b225847dd3ff59d648a1bc15ac4deb5b46404e47eef95e2ac417f6fccf582d84.
def localCycle00144 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 2, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, 0, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 0, .triangle 18 0, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint b3abc655a79c9597e9de5714ec73cef98444546face684442bb8df71feac3c74.
def localCycle00145 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 2 4, .distance 2 3]
    constant := ![-1, -1, 2, -2, -1, -1, 3, 0, 0, -1, -1, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, true, false, false, true, true] }
  origin := ![.triangle 15 0, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 29 1, .triangle 25 1]

-- Cycle fingerprint b494585c15fa3b0c9a6e18a300ae83fad2370415d325401b354b5ff4c793c017.
def localCycle00146 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint b6998aa4fdec881676ff57d279ce25c86e22a97ad1d12f4f279aba56952b6081.
def localCycle00147 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 6, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint b6a1b32f71c1f3e0da3378649323ecdc216e680edcd84f2dd1d10adcdf6df5a0.
def localCycle00148 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint b9b49d865886fca96b7bf3d06b3e5911efed76695c610bf92fb278dc6704379a.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 4 6, .distance 2 4, .distance 0 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 32 0, .triangle 29 0, .triangle 6 0, .triangle 7 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint b9c5ed7a8309868c9683d74de26a42a96e25cddfc47847da17878f8c2daa6f5c.
def localCycle00150 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 1 6, .distance 1 5, .distance 2 5]
    constant := ![0, 0, 3, 0, -1, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, true, false, true] }
  origin := ![.triangle 28 1, .gapLower 4 0, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 21 2, .gapLower 1 2, .triangle 17 1]

-- Cycle fingerprint ba0e7e7fb054d7fd5df26e1b19279b551979f82a0f5e288ce9f15beace834098.
def localCycle00151 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, -1, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint bc6769a1789f1fecdee7dff32b8ab21d94ca266262a745736945346e785926f9.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 6, .distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 6]
    constant := ![0, 0, -1, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, false, true, false, false, true, false] }
  origin := ![.triangle 30 1, .triangle 26 1, .corridorLower 2 3, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 16 1, .triangle 18 0]

-- Cycle fingerprint bcc7d6423ca382afec9568fbc1cad7b4291f2a4858743eccb5146fd0096758b7.
def localCycle00153 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 2 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 18 0, .triangle 29 1, .gapUpper 4 2]

-- Cycle fingerprint bcfd47754f5caa155bc816ec2c97810fdd42b58ca7b76875128d6175780e55b4.
def localCycle00154 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .zero]
    constant := ![0, 3, 0, -1, 0, 0, -1, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 20 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint bd07bb76ee4c697a4a1d4c28706764e27046c175300ce6de1ac0399c857e108b.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 5, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, true, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 1 4, .gapLower 5 0, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint be566382cc17d2e345b2c83cfec843ef1de7d12bf5f939ce5f798fe1e62b793e.
def localCycle00156 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, false, true, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 29 0, .triangle 13 0, .triangle 9 1, .triangle 10 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1, .thetaLower 1]

-- Cycle fingerprint c1d2cf55ff4e071b8036f0e3aca5d838047539fcd280080dff8356cb2a41d4f0.
def localCycle00157 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 3 5, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 11 0, .triangle 21 0, .triangle 20 0, .triangle 26 0, .gapLower 3 0]

-- Cycle fingerprint c25563cd3278d871e6695c8caa6d50ae30a9cfeaeeb346e69fc0e2296945dd7b.
def localCycle00158 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, -2, -2, -1, 0, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, false, false, true, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint c2754f2789fe8cf406bc603ad64592c72d0f1a84288be4f0f98c9730c7ca1cf3.
def localCycle00159 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, 0, -1, -1, 0, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, true, false, false, true, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .triangle 21 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint c27708eba4091d867227ae56067752fcbca0b70c155d8eda65c05a6ef8a976ac.
def localCycle00160 : Cycle where
  length := 5
  data := {
    node := ![.distance 2 6, .distance 4 6, .distance 1 4, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 29 1, .gapUpper 4 2, .triangle 16 1, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint c3fa3266719f43e263b7de315dc4f416a99ae669ceb0542dbd01c8d611377196.
def localCycle00161 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint c55cdfe2403613308600deaf75f6517b3e5e972797fb4f295adc5be4ea85375f.
def localCycle00162 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint c8aa123e88dae8890c464e11c57d2c46426878989418fb5e4e3cc61aebcde8ac.
def localCycle00163 : Cycle where
  length := 15
  data := {
    node := ![.distance 1 2, .distance 2 6, .distance 4 6, .distance 4 5, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![-1, 0, 0, -1, 3, 0, -1, 0, 0, -1, -1, -2, 3, -2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, true, false, true, true, false, false, false, false, false, true] }
  origin := ![.triangle 18 0, .triangle 29 1, .triangle 34 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 20 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint c97368e73e26d65cfeafe257581a87610abc46099546f76b63cc2d6f59776afe.
def localCycle00164 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 2, .triangle 30 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint ca1565d3807849d96384b10073d21f387d33a6ea6f5db6bcad5081e80418a728.
def localCycle00165 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 27 0, .triangle 15 0, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint cb498d7606254b76073df4be4c2423c7257397bf8c106cb70f5858a74e7855bb.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2, .distance 2 5]
    constant := ![0, -1, 0, 3, -2, 0, -2, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, false] }
  origin := ![.triangle 26 1, .corridorLower 2 3, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2, .gapLower 1 3, .triangle 17 0]

-- Cycle fingerprint cbbedb672fab911a146caf7c7646ef2a473d65a3c170c486f1dea28d2164e60f.
def localCycle00167 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint ccf9ae471efaeb702d6d0fa7036bf5884259c5e2b83dc6caf1a11c332b9fb191.
def localCycle00168 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1]

-- Cycle fingerprint ce19faa6dc5a6132fd57f439170a6199768b2afea48048bc9a52b3c232028e4d.
def localCycle00169 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint ced48a1e8c3cea2a26a2d6a2b946d6534bda193281ab82c93399e8933595773e.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1]
    constant := ![1, 0, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 5 2, .triangle 10 0, .triangle 20 0, .corridorLower 1 3]

-- Cycle fingerprint cedb3643a7179a6c732835114823618d3b651ebcdf922064e0239b178f98496d.
def localCycle00171 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2, .gapLower 1 2, .corridorLower 1 5]

-- Cycle fingerprint cf04bf42afdbfe8bdb302ee56c443ef2d26715be31d11fd6ecd44a1d765cca24.
def localCycle00172 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![0, -1, -1, 0, -3, 0, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, true, true, false, false, false, false, true] }
  origin := ![.triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint cf06a1358f39a1a324fad2ff367c3b317c21bc2e9ae71a80ff11f97a96d3a942.
def localCycle00173 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-1, 2, 0, 0, -1, 0, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 8 0, .triangle 30 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint cf71fc83d16f0439132916bd1528bc8e704045644e4ed1424845db6dca6f68ac.
def localCycle00174 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint cfe59859940d7804a0c118fcc394d1e7b5cefc571e405e0111e59bc55164fbfc.
def localCycle00175 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint d0c02935cee65de9c965c1001c0a9bf527348f1810265316d7a9cea226ca00a5.
def localCycle00176 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint d0ffbd03a129a0c6d6a7749d97c3ad51fc595adb46be7ec8f3893b6bc51212be.
def localCycle00177 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 16 1, .triangle 18 2, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint d132190683788d578ac59a31b32b234fcbcb72e552b6544ed2e1b88b12c43830.
def localCycle00178 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 1 6, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 16 1, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint d329bfdb5f0afd0679c6b3bdb6108eb9b8f499d97584ca6fc866e53696209651.
def localCycle00179 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, 0, 0, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 16 2, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint d517c8ff9316d2e7406beb38e93ce5654236f84b0c204ba2ecf23eb8a3fe039b.
def localCycle00180 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 2, .triangle 22 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint d5367272bf85b4745a7965ff3d4792f556d855bf0300a0726d7e5226cb8f0e3a.
def localCycle00181 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, -2, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false] }
  origin := ![.triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint d58788a1e9494a30e4f81bca13c9b0f076f783033b7c6255c65b321b27277660.
def localCycle00182 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 5, .distance 1 5, .distance 1 3, .distance 3 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 3, .gapLower 1 1, .gapUpper 3 2]

-- Cycle fingerprint d5f806249392e17c849c226acb19ad27c7841275bda759ba4a9bdd10b178f659.
def localCycle00183 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint d6471e1ba5b0162a4f5b98c3197c60de93ca8dab53d76a56c66fbcf71c453e1b.
def localCycle00184 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 2 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 4, .distance 3 4]
    constant := ![0, -1, 0, 0, -1, 0, -2, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 6 0, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 20 2, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 4, .corridorUpper 3 4]

-- Cycle fingerprint d7b8861f90f0a631687f0b85361b42b932169f816fd34888808f70a9c0d4abf4.
def localCycle00185 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 5 6, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 30 0, .triangle 14 0, .triangle 7 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00186 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint da9d6838a781e018e7759c6d48dcbe419f76dca46452c68e1e2a426627846871.
def localCycle00187 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 0 4, .distance 4 6, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, 0, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 2, .triangle 13 0, .triangle 29 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint dae9255c1d32885bf95dbfd508e347c132838a26326903bb88d30a8b466a6ac6.
def localCycle00188 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, 0, -1, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 29 0, .triangle 34 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1]

-- Cycle fingerprint db62f31b39028ea8680f29b9308af2f2dec9ace870048af6a863518d1ed63e19.
def localCycle00189 : Cycle where
  length := 13
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 5 6]
    constant := ![-1, 0, -2, -2, -1, 0, 0, 3, 0, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, true, false, false, true] }
  origin := ![.triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 30 1]

-- Cycle fingerprint dcbccf0f95fde8a444f9abdfccf746d38696192c79bfd33604e347eed075fdfc.
def localCycle00190 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 0, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dcfbdd449d7d59a8f5d39a99649f49aa1bfaf379eb039477589fa201898de499.
def localCycle00191 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 27 0, .gapLower 3 0]

-- Cycle fingerprint e099760a670dea0d6c714bd48159f206b00aa1759c1d36f980ed2260d4698273.
def localCycle00192 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6]
    constant := ![0, -1, -2, 0, -2, -1, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, false, false, false, false, true, true, false, false] }
  origin := ![.triangle 30 1, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0]

-- Cycle fingerprint e23c3e5edff047fc02a422b8a5bd793b705e84cb96e6670989de02fb81e1ed8b.
def localCycle00193 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint e2b66063a93cbc068573e823cc51ba036775f31582bed56cdbe31049ed87d019.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint e32ae6bd7cf0ba7c5a9ec967e7ecf1c09bd8ec6a70bc41f87e962c8e155faaea.
def localCycle00195 : Cycle where
  length := 13
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 4]
    constant := ![-1, -1, 0, -1, 0, -1, 3, -1, -1, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 13 0, .triangle 23 0, .gapLower 1 3, .triangle 17 0, .triangle 28 1, .corridorLower 4 5, .corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .corridorLower 1 3, .corridorUpper 0 1, .triangle 2 2]

-- Cycle fingerprint e347cc187b6dea0b97bf643357e60edd8f3df4d1dade297c306c715aa403cf8f.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 1 2, .distance 2 3, .theta 3]
    constant := ![4, -1, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 6, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 16 0, .triangle 15 0, .gapLower 3 0]

-- Cycle fingerprint e40ae0c84a705b3ea219c3432df57438f0b27f12ccfa25a999241eaa9fa78e01.
def localCycle00197 : Cycle where
  length := 3
  data := {
    node := ![.distance 2 6, .distance 1 2, .distance 1 6, .distance 2 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 2 3, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint e455824697edbb63013b0d9260fde7029d275823c3531b326b6259fd8feedd2a.
def localCycle00198 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 3, .distance 3 5, .distance 2 3, .theta 2, .theta 1]
    constant := ![3, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 15 2, .triangle 20 0, .triangle 26 0, .corridorLower 2 3, .thetaNext 1]

-- Cycle fingerprint e4b4f33d1377c5c7c758fe6d73ccce0fc927ddee5591d2de097d72165e639991.
def localCycle00199 : Cycle where
  length := 13
  data := {
    node := ![.distance 2 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6]
    constant := ![0, 0, -2, -2, -1, 0, 0, 0, 3, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true, false, false, false, true, true, false, false] }
  origin := ![.triangle 18 2, .triangle 23 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0]

-- Cycle fingerprint e50b3401a62cf6eed39251c7822a1f1fed91a4d2048722521ffd26246b4e14e9.
def localCycle00200 : Cycle where
  length := 11
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -2, 3, -2, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 16 1, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint e700ff62e90dde339dbdea71144523d585b35a149f41615a8ab711d8f9508462.
def localCycle00201 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 3, .distance 3 6, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 3]
    constant := ![-1, 0, -1, -1, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, true] }
  origin := ![.triangle 11 0, .triangle 33 1, .triangle 20 0, .corridorLower 1 3, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 5 2]

-- Cycle fingerprint e7ca81d31fdb9b7449effe18fe1f9338a09e97947b15e4b9f8e440898af5cb21.
def localCycle00202 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6]
    constant := ![-2, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2]

-- Cycle fingerprint e8026a1b17c95e36f72b461bcfab3eba5d5e746dff224cc323384a3fea8340c8.
def localCycle00203 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 6, .distance 0 3, .distance 3 5, .distance 1 5, .distance 1 3]
    constant := ![-1, 2, 0, 0, 0, 0, -1, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false, true, false] }
  origin := ![.corridorLower 1 3, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 8 2, .triangle 11 1, .triangle 10 0, .triangle 20 2, .gapLower 1 1]

-- Cycle fingerprint ea4f45317caf86baf347ffc924654b245f0c7989b5f671e66426ef5fd48f8e60.
def localCycle00204 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 6, .distance 0 3, .distance 3 5, .distance 1 3, .theta 1, .distance 0 1, .distance 0 4, .distance 0 2, .distance 0 6]
    constant := ![0, -1, -1, -2, 2, 0, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, true, true, true] }
  origin := ![.triangle 11 1, .triangle 10 0, .triangle 20 0, .gapLower 1 0, .gapLower 1 6, .triangle 2 2, .triangle 6 1, .triangle 8 2]

-- Cycle fingerprint eb7dd4fa305ecafc416eff62e95582fc0ec6ab99a079ec13efe978614f8c346f.
def localCycle00205 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 5, .distance 1 3]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .gapLower 1 2, .triangle 20 1]

-- Cycle fingerprint ec5882f211b2346368e6314a53f5da43123641f7d3e2c213421194f7566f61ff.
def localCycle00206 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![-2, -2, -1, 4, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .gapLower 1 1, .corridorLower 1 3, .gapLower 1 6, .triangle 2 0, .triangle 16 1, .triangle 18 2]

-- Cycle fingerprint eda5f514c8e079be803b612acd283a4e526c3d4f36abac9d1717ee343b5373a6.
def localCycle00207 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1]
    constant := ![2, 0, 0, -1, 0, -1, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 7 1, .triangle 6 0, .triangle 25 1, .triangle 15 0, .gapLower 1 0]

-- Cycle fingerprint f0b4502b0c4166ba85fd7e8a7efe5f284d22eae185384d5b8b75d4dbe490d7a8.
def localCycle00208 : Cycle where
  length := 12
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .theta 1, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false, true, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .corridorLower 1 2, .thetaNext 0, .thetaLower 0]

-- Cycle fingerprint f0d230c19d647462804039d5e115fca0a8d3d91e9e892c3a265be4e340cc20d0.
def localCycle00209 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 28 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint f1309f3b5e43f537d3d64dff0430d186baca95743b88a4de1aa087ace16d7431.
def localCycle00210 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint f191cb4cccf17edbf56491373011763b04479d84e0f5485b12d37fb83f91e1bf.
def localCycle00211 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 5, .distance 5 6, .distance 2 5, .distance 1 2, .distance 2 3, .theta 2, .zero]
    constant := ![0, 3, 0, -1, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 4, .corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 7 2, .triangle 14 0, .triangle 30 0, .triangle 17 0, .triangle 15 0, .corridorLower 2 3, .thetaLower 2]

-- Cycle fingerprint f2844c1d6335cb305104b656374f169d731caaf1d32d6c858c58a10089487ffb.
def localCycle00212 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 8 0, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint f34fd7af36d02f599b969821f2e7288927dc344f25f7b7546d1325ffe1fa70e9.
def localCycle00213 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint f55dde6233a9bbe4b063e56852ea082281522e9be247f616c047dcbb510d1e3c.
def localCycle00214 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint f5f7a412c9de36cf8dda5bf30644482bbe21742eec3940aa4626f826123b9f7c.
def localCycle00215 : Cycle where
  length := 12
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 4, .distance 2 3, .distance 1 2, .distance 2 6, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -1, -1, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false, true, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 6 0, .triangle 25 1, .triangle 15 0, .triangle 18 0, .triangle 27 1, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint f611c6b82844802432a2085d2047c6f80be9d2e32d29dea3df69c86e2b5620b6.
def localCycle00216 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 20 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 16 1, .triangle 18 2]

-- Cycle fingerprint f736a19642c06d756f7dfcf9b5a60f820a3fd4e7ec6d122bd44d3ce5ba8c5498.
def localCycle00217 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 2, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 16 1, .gapLower 1 2, .corridorLower 1 5, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint f862b1d210faed7f302b620cf09910a7b3bb5ae245c5d01eeb3b200f3fc9280a.
def localCycle00218 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![4, -1, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.gapLower 4 6, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 33 1, .triangle 34 0, .gapLower 4 0]

-- Cycle fingerprint f917ec9de1f23ce0ef60afdea9f490037be423f188bd4440f747d7c7dac9810d.
def localCycle00219 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 2, .distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 16 1, .triangle 18 2, .triangle 24 1, .gapLower 1 1, .corridorLower 1 3, .corridorUpper 0 1]

-- Cycle fingerprint fb3e9c62ce7bc48d6cd0d2498f2edd39bc8e7a9643310cac727915a9f14adda6.
def localCycle00220 : Cycle where
  length := 10
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 4, .distance 0 2, .distance 0 3, .distance 3 6, .distance 2 6, .distance 1 2, .distance 2 5, .distance 4 5, .theta 4]
    constant := ![3, 0, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 2, .triangle 6 0, .triangle 5 2, .triangle 11 0, .triangle 27 2, .triangle 18 0, .triangle 17 0, .triangle 28 1, .corridorLower 4 5]

-- Cycle fingerprint fc81817b37ab1ff310868912dd1214e511719270222f2c2699624a91409bc3a0.
def localCycle00221 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 1 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 20 0, .triangle 21 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint fd3ba523112913f3a2c25a755f61b80b1e557224fc91d84f7ee00a3dec6ce484.
def localCycle00222 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint fd57bb75fd3624fdab0b024561ed4609f08df9c0bae8a8494f4ae5ffd69a3593.
def localCycle00223 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 5, .distance 0 2, .distance 2 6, .distance 1 6, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, 0, -1, -1, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 2, .triangle 7 0, .triangle 8 0, .triangle 18 2, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint fd9f249f7f6bdac201f804ae5cf72c2f02c5a22e809ba5af8a309cc3ad93aed2.
def localCycle00224 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 2 5, .distance 1 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, 0, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 26 2, .triangle 17 2, .triangle 24 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint fdc9138c1dc50a34bf20f0daedd4a326d21420e986129f1cadb067a713ab1cb4.
def localCycle00225 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 6, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![0, -1, -1, -2, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 7 1, .triangle 8 0, .triangle 18 0, .gapLower 1 0, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint fe3c1f1b984d63ef8e457e7a35b01f491f4a848d754a64b8d0d659c47230ae83.
def localCycle00226 : Cycle where
  length := 10
  data := {
    node := ![.distance 0 5, .distance 0 2, .distance 2 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![0, -1, 0, -1, 0, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, false, true] }
  origin := ![.triangle 7 1, .triangle 8 0, .triangle 30 1, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2]

def library : Library := fun id => if id < 113 then (if id < 56 then (if id < 28 then (if id < 14 then (if id < 7 then (if id < 3 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id < 2 then (if id = 1 then some localCycle00001 else none) else (if id = 2 then some localCycle00002 else none))) else (if id < 5 then (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)) else (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id = 6 then some localCycle00006 else none)))) else (if id < 10 then (if id < 8 then (if id = 7 then some localCycle00007 else none) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id = 9 then some localCycle00009 else none))) else (if id < 12 then (if id < 11 then (if id = 10 then some localCycle00010 else none) else (if id = 11 then some localCycle00011 else none)) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))))) else (if id < 21 then (if id < 17 then (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none))) else (if id < 19 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id = 18 then some localCycle00018 else none)) else (if id < 20 then (if id = 19 then some localCycle00019 else none) else (if id = 20 then some localCycle00020 else none)))) else (if id < 24 then (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id < 23 then (if id = 22 then some localCycle00022 else none) else (if id = 23 then some localCycle00023 else none))) else (if id < 26 then (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none)) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id = 27 then some localCycle00027 else none)))))) else (if id < 42 then (if id < 35 then (if id < 31 then (if id < 29 then (if id = 28 then some localCycle00028 else none) else (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id = 30 then some localCycle00030 else none))) else (if id < 33 then (if id < 32 then (if id = 31 then some localCycle00031 else none) else (if id = 32 then some localCycle00032 else none)) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none)))) else (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 40 then (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id = 39 then some localCycle00039 else none)) else (if id < 41 then (if id = 40 then some localCycle00040 else none) else (if id = 41 then some localCycle00041 else none))))) else (if id < 49 then (if id < 45 then (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id < 44 then (if id = 43 then some localCycle00043 else none) else (if id = 44 then some localCycle00044 else none))) else (if id < 47 then (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none)) else (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)))) else (if id < 52 then (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none))) else (if id < 54 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id = 53 then some localCycle00053 else none)) else (if id < 55 then (if id = 54 then some localCycle00054 else none) else (if id = 55 then some localCycle00055 else none))))))) else (if id < 84 then (if id < 70 then (if id < 63 then (if id < 59 then (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id < 58 then (if id = 57 then some localCycle00057 else none) else (if id = 58 then some localCycle00058 else none))) else (if id < 61 then (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none)) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id = 62 then some localCycle00062 else none)))) else (if id < 66 then (if id < 64 then (if id = 63 then some localCycle00063 else none) else (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id = 65 then some localCycle00065 else none))) else (if id < 68 then (if id < 67 then (if id = 66 then some localCycle00066 else none) else (if id = 67 then some localCycle00067 else none)) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none))))) else (if id < 77 then (if id < 73 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 75 then (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id = 74 then some localCycle00074 else none)) else (if id < 76 then (if id = 75 then some localCycle00075 else none) else (if id = 76 then some localCycle00076 else none)))) else (if id < 80 then (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id < 79 then (if id = 78 then some localCycle00078 else none) else (if id = 79 then some localCycle00079 else none))) else (if id < 82 then (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none)) else (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id = 83 then some localCycle00083 else none)))))) else (if id < 98 then (if id < 91 then (if id < 87 then (if id < 85 then (if id = 84 then some localCycle00084 else none) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id = 86 then some localCycle00086 else none))) else (if id < 89 then (if id < 88 then (if id = 87 then some localCycle00087 else none) else (if id = 88 then some localCycle00088 else none)) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none)))) else (if id < 94 then (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none))) else (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id = 97 then some localCycle00097 else none))))) else (if id < 105 then (if id < 101 then (if id < 99 then (if id = 98 then some localCycle00098 else none) else (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id = 100 then some localCycle00100 else none))) else (if id < 103 then (if id < 102 then (if id = 101 then some localCycle00101 else none) else (if id = 102 then some localCycle00102 else none)) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none)))) else (if id < 109 then (if id < 107 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id = 106 then some localCycle00106 else none)) else (if id < 108 then (if id = 107 then some localCycle00107 else none) else (if id = 108 then some localCycle00108 else none))) else (if id < 111 then (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)) else (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id = 112 then some localCycle00112 else none)))))))) else (if id < 170 then (if id < 141 then (if id < 127 then (if id < 120 then (if id < 116 then (if id < 114 then (if id = 113 then some localCycle00113 else none) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id = 115 then some localCycle00115 else none))) else (if id < 118 then (if id < 117 then (if id = 116 then some localCycle00116 else none) else (if id = 117 then some localCycle00117 else none)) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none)))) else (if id < 123 then (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none))) else (if id < 125 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id = 124 then some localCycle00124 else none)) else (if id < 126 then (if id = 125 then some localCycle00125 else none) else (if id = 126 then some localCycle00126 else none))))) else (if id < 134 then (if id < 130 then (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id < 129 then (if id = 128 then some localCycle00128 else none) else (if id = 129 then some localCycle00129 else none))) else (if id < 132 then (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none)) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id = 133 then some localCycle00133 else none)))) else (if id < 137 then (if id < 135 then (if id = 134 then some localCycle00134 else none) else (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id = 136 then some localCycle00136 else none))) else (if id < 139 then (if id < 138 then (if id = 137 then some localCycle00137 else none) else (if id = 138 then some localCycle00138 else none)) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none)))))) else (if id < 155 then (if id < 148 then (if id < 144 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 146 then (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id = 145 then some localCycle00145 else none)) else (if id < 147 then (if id = 146 then some localCycle00146 else none) else (if id = 147 then some localCycle00147 else none)))) else (if id < 151 then (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id < 150 then (if id = 149 then some localCycle00149 else none) else (if id = 150 then some localCycle00150 else none))) else (if id < 153 then (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none)) else (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id = 154 then some localCycle00154 else none))))) else (if id < 162 then (if id < 158 then (if id < 156 then (if id = 155 then some localCycle00155 else none) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id = 157 then some localCycle00157 else none))) else (if id < 160 then (if id < 159 then (if id = 158 then some localCycle00158 else none) else (if id = 159 then some localCycle00159 else none)) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none)))) else (if id < 166 then (if id < 164 then (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id = 163 then some localCycle00163 else none)) else (if id < 165 then (if id = 164 then some localCycle00164 else none) else (if id = 165 then some localCycle00165 else none))) else (if id < 168 then (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none)) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id = 169 then some localCycle00169 else none))))))) else (if id < 198 then (if id < 184 then (if id < 177 then (if id < 173 then (if id < 171 then (if id = 170 then some localCycle00170 else none) else (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id = 172 then some localCycle00172 else none))) else (if id < 175 then (if id < 174 then (if id = 173 then some localCycle00173 else none) else (if id = 174 then some localCycle00174 else none)) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none)))) else (if id < 180 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 182 then (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id = 181 then some localCycle00181 else none)) else (if id < 183 then (if id = 182 then some localCycle00182 else none) else (if id = 183 then some localCycle00183 else none))))) else (if id < 191 then (if id < 187 then (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id < 186 then (if id = 185 then some localCycle00185 else none) else (if id = 186 then some localCycle00186 else none))) else (if id < 189 then (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none)) else (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)))) else (if id < 194 then (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none))) else (if id < 196 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id = 195 then some localCycle00195 else none)) else (if id < 197 then (if id = 196 then some localCycle00196 else none) else (if id = 197 then some localCycle00197 else none)))))) else (if id < 212 then (if id < 205 then (if id < 201 then (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id < 200 then (if id = 199 then some localCycle00199 else none) else (if id = 200 then some localCycle00200 else none))) else (if id < 203 then (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none)) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id = 204 then some localCycle00204 else none)))) else (if id < 208 then (if id < 206 then (if id = 205 then some localCycle00205 else none) else (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id = 207 then some localCycle00207 else none))) else (if id < 210 then (if id < 209 then (if id = 208 then some localCycle00208 else none) else (if id = 209 then some localCycle00209 else none)) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none))))) else (if id < 219 then (if id < 215 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none))) else (if id < 217 then (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id = 216 then some localCycle00216 else none)) else (if id < 218 then (if id = 217 then some localCycle00217 else none) else (if id = 218 then some localCycle00218 else none)))) else (if id < 223 then (if id < 221 then (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none)) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id = 222 then some localCycle00222 else none))) else (if id < 225 then (if id < 224 then (if id = 223 then some localCycle00223 else none) else (if id = 224 then some localCycle00224 else none)) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none))))))))

def namedLeaf000 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 4, 5, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 5, 0, 4], ![6, 1, 5, 0, 2, 3], ![6, 1, 4, 2, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 23 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20864)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 5, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 1, 2, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 114 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20865)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 4, 6], ![2, 1, 5, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 1, 2, 3, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 60 }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20866)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 9 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20867)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 101 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20868)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 129 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20869)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 91 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20870)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 1 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20871)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 137 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20872)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 49 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20873)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 53 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20874)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 2, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 186 }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20875)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 4, 6, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 1, 6, 2, 3, 0], ![1, 4, 5, 2, 3, 0]], proof := .tail 46 }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20876)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 3, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 211 }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20877)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 5, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 2, 6, 3, 0], ![4, 1, 2, 5, 3, 0]], proof := .tail 186 }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20878)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 5, 6, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 1, 6, 2, 3, 0], ![4, 1, 5, 2, 3, 0]], proof := .tail 46 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20879)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 1, 2, 3, 0]], proof := .tail 224 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20880)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 2, 1, 3, 0]], proof := .tail 144 }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20881)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 164 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20882)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 1, 2, 3, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 112 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20883)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 2, 6, 5, 4, 0], ![3, 1, 6, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 1, 2, 3, 0]], proof := .tail 85 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20884)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 2, 1, 3, 0]], proof := .tail 33 }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20885)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![3, 6, 1, 5, 0, 4], ![2, 6, 1, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 191 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20886)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 2, 5, 4, 0], ![6, 3, 1, 5, 0, 4], ![6, 2, 1, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 1, 2, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 23 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20887)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 1, 5, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 2, 1, 3, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 130 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20888)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 1, 5, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 2, 1, 3, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 149 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20889)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 2, 1, 3, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 156 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20890)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 195 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20891)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 0, 6, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .low (![50, 182, 111, 113, 169, 99, 170, 51, 205, 96, 22, 200, 81, 45, 56, 11, 31, 106, 132, 148, 168, 217, 28, 166, 63, 70, 3, 0]) }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20892)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 212 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20893)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 212 }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20894)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 5, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .low (![154, 182, 171, 197, 153, 32, 7, 184, 216, 21, 127, 163, 204, 206, 160, 127, 219, 203, 160, 127, 35, 177, 127, 147, 178, 127, 127, 152]) }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20895)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 193 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20896)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 220 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20897)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .low (![42, 182, 48, 197, 153, 32, 142, 8, 12, 21, 127, 27, 90, 150, 160, 127, 219, 25, 160, 127, 35, 201, 127, 147, 178, 127, 127, 152]) }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20898)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 3, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 58 }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20899)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 1, 6, 3, 0], ![1, 4, 2, 5, 3, 0]], proof := .tail 186 }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20900)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 58 }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20901)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 3, 0], ![4, 1, 2, 5, 3, 0]], proof := .tail 186 }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20902)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 5, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 3, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 54 }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20903)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 5, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 1, 6, 3, 0], ![4, 2, 1, 5, 3, 0]], proof := .tail 186 }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20904)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 1, 3, 0], ![4, 2, 5, 1, 3, 0]], proof := .tail 15 }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20905)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 2, 1, 3, 0]], proof := .tail 15 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20906)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 6, 1, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 1, 3, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 218 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20907)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 164 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20908)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 5, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 1, 3, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 218 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20909)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![3, 6, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 1, 6, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 2, 1, 3, 0]], proof := .tail 180 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20910)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 1, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 191 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20911)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 3, 5, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 1, 5, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 1, 3, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 221 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20912)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 5, 1, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 2, 3, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 133 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20913)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 0, 4, 6], ![2, 5, 1, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 2, 3, 1, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 149 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20914)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 5, 1, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 2, 3, 1, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 10 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20915)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 0, 6, 4], ![2, 5, 1, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 98 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20916)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 0, 6, 4], ![2, 5, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 198 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20917)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 62 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20918)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 62 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20919)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 95 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20920)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 157 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20921)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 44 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20922)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 64 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20923)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 115 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20924)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 2, 3, 1, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 136 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20925)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![3, 5, 1, 6, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 136 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20926)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 136 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20927)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 41 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20928)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 5, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 3, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 17 }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20929)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![3, 5, 6, 1, 0, 4], ![2, 6, 5, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 2, 6, 3, 1, 0], ![4, 2, 5, 3, 1, 0]], proof := .tail 186 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20930)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 5, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 2, 3, 1, 0]], proof := .tail 46 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20931)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 5, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 2, 3, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 162 }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20932)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![3, 6, 5, 1, 0, 4], ![2, 6, 5, 1, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 2, 3, 1, 0]], proof := .tail 209 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20933)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![6, 3, 5, 1, 0, 4], ![6, 2, 5, 1, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 2, 3, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 65 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20934)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 0, 4, 6], ![5, 2, 1, 0, 4, 6], ![5, 1, 0, 2, 3, 6], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 18 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20935)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 0, 4, 6], ![5, 2, 1, 0, 6, 4], ![5, 1, 0, 2, 6, 3], ![4, 3, 2, 1, 0, 6], ![1, 0, 2, 4, 3, 5]], proof := .tail 40 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20936)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![5, 3, 2, 4, 6, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 0, 6, 4], ![5, 2, 1, 0, 6, 4], ![5, 1, 0, 6, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 0, 4, 2, 3, 5]], proof := .tail 19 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20937)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 0, 6, 4], ![5, 2, 1, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 0, 2, 3, 5]], proof := .tail 24 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20938)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![5, 3, 2, 6, 4, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 0, 6, 4], ![5, 2, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 0, 2, 3, 5]], proof := .tail 141 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20939)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 0, 6, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 0, 3, 5]], proof := .tail 135 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20940)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 0, 3, 5]], proof := .tail 135 }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20941)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![5, 3, 6, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 1, 0, 6, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 0, 3, 5]], proof := .tail 83 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20942)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![1, 4, 2, 3, 0, 5]], proof := .tail 59 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20943)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 1, 2, 3, 0, 5]], proof := .tail 59 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20944)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 1, 3, 0, 5]], proof := .tail 109 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20945)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 2, 3, 1, 0, 5]], proof := .tail 43 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20946)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![5, 6, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![5, 6, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 0, 6], ![4, 3, 2, 1, 0, 5]], proof := .tail 57 }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20947)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 2, 4, 6, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 1, 6, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![1, 4, 2, 3, 5, 0]], proof := .tail 126 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20948)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 2, 6, 4, 0], ![5, 3, 1, 6, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 1, 2, 3, 5, 0]], proof := .tail 126 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20949)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 3, 6, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 1, 6, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 1, 3, 5, 0]], proof := .tail 119 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20950)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 2, 3, 1, 5, 0]], proof := .tail 119 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20951)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![5, 6, 3, 2, 4, 0], ![5, 6, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 1, 6, 0], ![4, 3, 2, 1, 5, 0]], proof := .tail 100 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20952)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![5, 3, 6, 1, 0, 4], ![5, 2, 6, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 6, 1, 0], ![4, 2, 3, 5, 1, 0]], proof := .tail 119 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20953)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![5, 6, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 2, 6, 1, 0], ![4, 3, 2, 5, 1, 0]], proof := .tail 100 }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20954)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![6, 5, 3, 1, 0, 4], ![5, 6, 2, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 6, 2, 1, 0], ![4, 3, 5, 2, 1, 0]], proof := .tail 190 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20955)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![6, 5, 3, 1, 0, 4], ![6, 5, 2, 1, 0, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 3, 2, 1, 0], ![4, 5, 3, 2, 1, 0]], proof := .tail 6 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20956)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![6, 5, 3, 2, 4, 1], ![6, 5, 3, 2, 4, 0], ![6, 5, 3, 1, 0, 4], ![6, 5, 2, 1, 0, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 3, 2, 1, 0], ![5, 4, 3, 2, 1, 0]], proof := .tail 77 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20957)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 4, 5, 6], ![1, 2, 0, 3, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 93 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20958)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 4, 5, 6], ![1, 2, 0, 3, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 151 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20959)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 208 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20960)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 185 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20961)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .low (![167, 139, 213, 117, 66, 214, 122, 26, 76, 76, 76, 76, 207, 103, 194, 87, 181, 116, 125, 175, 143, 55, 202, 29, 55, 16, 55, 55]) }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20962)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![167, 139, 179, 78, 89, 67, 122, 120, 108, 76, 76, 84, 207, 174, 210, 92, 107, 121, 161, 69, 68, 79, 176, 5, 55, 222, 146, 13]) }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20963)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 5, 6], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 4, 3]], proof := .tail 134 }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20964)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 4, 3]], proof := .tail 30 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20965)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 4, 3]], proof := .tail 36 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20966)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 0, 6, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 4, 3]], proof := .tail 36 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20967)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 3, 4]], proof := .low (![39, 139, 118, 124, 66, 214, 88, 159, 110, 38, 102, 4, 225, 189, 192, 155, 61, 226, 20, 155, 71, 173, 155, 105, 128, 16, 73, 73]) }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20968)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 0, 4, 3]], proof := .tail 80 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20969)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 0, 3]], proof := .tail 187 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20970)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 0, 3]], proof := .tail 188 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20971)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 2, 4, 3, 0]], proof := .tail 165 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20972)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 2, 3, 0]], proof := .tail 165 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20973)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 3, 2, 0]], proof := .tail 123 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20974)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 3, 4]], proof := .low (![39, 139, 94, 172, 89, 72, 88, 159, 14, 223, 34, 4, 225, 199, 52, 47, 131, 82, 158, 2, 68, 73, 138, 5, 73, 222, 146, 145]) }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20975)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![3, 4, 6, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 0, 6, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 0, 4, 3]], proof := .tail 80 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20976)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 0, 3]], proof := .tail 187 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20977)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 0, 3]], proof := .tail 74 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20978)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![3, 6, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 0, 6, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 0, 3]], proof := .tail 97 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20979)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 4, 6, 0, 5], ![1, 2, 6, 0, 4, 5], ![1, 2, 6, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 2, 4, 3, 0]], proof := .tail 165 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20980)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 2, 3, 0]], proof := .tail 165 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20981)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 4, 5], ![1, 6, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 3, 2, 0]], proof := .tail 123 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20982)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 3, 6, 4, 0, 5], ![1, 2, 6, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 2, 3, 0]], proof := .tail 165 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20983)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 6, 3, 4, 0, 5], ![1, 6, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 3, 2, 0]], proof := .tail 37 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20984)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 6, 3, 4, 0, 5], ![6, 1, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 2, 0]], proof := .tail 86 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20985)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![6, 3, 4, 2, 5, 1], ![6, 2, 3, 4, 5, 0], ![6, 1, 3, 4, 0, 5], ![6, 1, 2, 0, 4, 5], ![6, 1, 2, 0, 3, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 2, 1, 0]], proof := .tail 215 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20986)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 4, 5, 6], ![1, 2, 0, 3, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 183 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20987)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 4, 5, 6], ![1, 2, 0, 3, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 140 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20988)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 5, 6], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 196 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20989)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![3, 4, 2, 5, 6, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .tail 104 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20990)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![3, 4, 2, 6, 5, 1], ![3, 2, 4, 5, 6, 0], ![3, 1, 4, 0, 6, 5], ![2, 1, 0, 4, 6, 5], ![1, 2, 0, 3, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .tail 75 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 20991)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

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
end Jsp404.N4R2OuterLeftData.LeafShard163
