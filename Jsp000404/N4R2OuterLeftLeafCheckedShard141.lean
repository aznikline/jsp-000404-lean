import Jsp000404.N4R2OuterLeftReplay
import Jsp000404.N4R2WordCatalog

set_option autoImplicit false
set_option pp.fullNames true
set_option maxRecDepth 8192
set_option maxHeartbeats 0
set_option Elab.async false

namespace Jsp404.N4R2OuterLeftData.LeafShard141
open N4R2OuterLeftReplay

-- Cycle fingerprint 0061eb0e3c1f4123ea43847e38e6a0691ccc32b692ab51fb001a0efc660824f1.
def localCycle00000 : Cycle where
  length := 11
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 015ae997564c721ed4519130540bce7fd3208eeb7a653670d01a82870c05b2d0.
def localCycle00001 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 01b275edd372d18769cecfd1c265e127f85bf4fa56d8784d327d633e068a93db.
def localCycle00002 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6]
    constant := ![0, -2, 0, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 6 1, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0]

-- Cycle fingerprint 01cc171d0d741b54db2a08d06e47765986a7486d9b3d98b35401efb513083c07.
def localCycle00003 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, 0, -1, -1, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 0275d29d4f54842beb9cacc33bbebf4dc6884b349b00c4af26e35360e1cb3998.
def localCycle00004 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, -1, -1, 0, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 0310ff91b2389153a1c2728f6df594b74a2179188755e0388c2847cc91b9632b.
def localCycle00005 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint 0380231bb4af12efbcb6bbc1e8fb7c9534ef4ccbf356695c07619a2ac87ef331.
def localCycle00006 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 03c47046f7e05877a51d898810632daeffdc30b21f12253f6db94af585c67aa7.
def localCycle00007 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 058c996f7c1a94dd55bb5c27185dedead134ba9900542079b81e1a0105a03fbc.
def localCycle00008 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .gapLower 3 0]

-- Cycle fingerprint 0625f28701ed9aaf86a20dd5087323a4311453cfe893a8a3da0a3edb8061ac90.
def localCycle00009 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-2, -2, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 19 1]

-- Cycle fingerprint 0648486c8d52a96ddb39e786d2d965de27fba9586b6ab2f7c0fcea5035e9d076.
def localCycle00010 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .triangle 22 1, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 06730242989941dbff2fade7f7299ceaa8afbe07f39f0d5107e58fd10a551dfa.
def localCycle00011 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![0, 0, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 07a7f6ebd377f1fa945f73d928cdc2d634164072885d8b8a1ce0df1323fc4e24.
def localCycle00012 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, 0, -1, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 07a978c3c9c6183724e92af296a2ea282f69eb273b55865f202306c04c1e2a54.
def localCycle00013 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 2]

-- Cycle fingerprint 0828610ff5e98a697371091d73d174540220c2091e773a5a384ddf1ba462a946.
def localCycle00014 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 086fae9efce582a1683bdcef7bd91b027f8070895e821c8c0845cf5661e5921e.
def localCycle00015 : Cycle where
  length := 6
  data := {
    node := ![.distance 4 5, .theta 4, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, 2, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 4 5, .thetaLower 4, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 0]

-- Cycle fingerprint 0a0bee7146b072bfa2cf294e9fc513ae5ab31663bba07056fa4370020ee645ad.
def localCycle00016 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 5, .distance 1 4, .distance 4 5]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 5 1, .gapLower 1 3, .gapUpper 4 1]

-- Cycle fingerprint 0aa8ffee5ed8ef2eb58a2664ae6c2a57b6c25fad15f62ba1c4e82ac24750bb0b.
def localCycle00017 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 5, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 28 1, .triangle 31 0, .triangle 9 0, .triangle 5 1]

-- Cycle fingerprint 0b36a762c2ea95477bb23fe83b0cc16f3eed8175af8ace166ed2e47ff74c5ff1.
def localCycle00018 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 2, 0, -1, 0, -2, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, true] }
  origin := ![.corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint 0d541cf2a74a2fa6cc4f94137bcec7e7739b1465a34c6cdec5bdb45ae259c8d3.
def localCycle00019 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 13 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint 0e0dfeee4cfa81d0dd53e8dcd5aa5c05dcc6ee3487d84302237c1c2c61c39a70.
def localCycle00020 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 24 1, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 0ef6d30578878f7db4047bbf96f7393553b90f0f542217ad2675f85671ab4568.
def localCycle00021 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, -1, -2, 0, -2, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, true, false, false, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 0ff1fcbadcd05b5087ee7fb0df9029157acd6763d83d81cff45a4aedbb91006e.
def localCycle00022 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, 0, -2, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 10554460a808c931f4a900d947160179b614486d9fa30613f6d3445d9dc308c8.
def localCycle00023 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![-1, 0, -1, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, false, false, false] }
  origin := ![.triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 2, .gapLower 1 3, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint 1078ced40a2e84ee8fe73fd0b28ddd9347b33ac9bd6281f4c9505900d9c21d5a.
def localCycle00024 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, -1, 0, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, true, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint 10c92406e05f0d3d5862da82cd74ae987efdd53da7d5b8ab88fc3b05add81910.
def localCycle00025 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint 10e8fb0afe18839c0416f36c58401ff15371f54ed39317e8e3d63626bcbccb52.
def localCycle00026 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .gapLower 3 0]

-- Cycle fingerprint 11ca1fb6bcbf6abd76d1466af0c5c4b3fc6d0a070144129d4fcab13ffe3a7371.
def localCycle00027 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint 13cfc6c1ef424113de01fe3ff46d62830c7d355135bb0e8a33f566d58001e819.
def localCycle00028 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 6]

-- Cycle fingerprint 14a9803b9e46a0c197c433a93b04d45c24fc5e635258914fea426660d63fbff4.
def localCycle00029 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 1507574cf625adb871faa7326dd78eb5b9419adcc9f22d1a96f6173ac35fb53f.
def localCycle00030 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -3, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 15ca5eb55c3a138ccf283b539eefc0d9d214ad2d99bef341c0f63d124c05ff24.
def localCycle00031 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![-1, 0, -1, -2, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 26 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0]

-- Cycle fingerprint 1671daf3bffc6eb638988bc5287a094b2ca1caafecbe9ea4ee1e39d9c5fef712.
def localCycle00032 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 6, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 6, .corridorUpper 0 1, .gapLower 1 5, .triangle 19 1]

-- Cycle fingerprint 16a128c9bdd81f0fd1382acc8bc919878a71328fcb4c69fe893b1087053c5903.
def localCycle00033 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, -2, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint 16e9a7044a17c268384bc44d854ae1732eb16338f27a22d899241105dcca9c44.
def localCycle00034 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, 0, -2, -2]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 17317a5f9ff012c52e3a733d55433627c645a8094335c4833f15ad1b991d5684.
def localCycle00035 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 13 0, .triangle 12 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint 179a23178912cf1459ee19d36a1b2aea640ec110c0ca68f480372d6b5b24861e.
def localCycle00036 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint 18f97c5054113df16e1435214476a477bdacd661a5fadbec8a95f2a51dff54df.
def localCycle00037 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, -1, -1, 0, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 195be1b48aa6290b889b664d65a2459be4f142f6536b3f7ef7e12d0a8923af58.
def localCycle00038 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 5, .corridorUpper 0 1]

-- Cycle fingerprint 196e89634f0b909815a13395fa68b1b4bce2142a26687711baf70d7b4409d98f.
def localCycle00039 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![1, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 197e9ae2c12b750db819b1b33bc66fc1965b345b35dacc6fb9dd10bab089de77.
def localCycle00040 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.triangle 26 0, .triangle 33 0, .gapLower 6 2, .triangle 4 1, .gapLower 1 4, .triangle 20 1, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint 198f9caeae35f75a5e2208b622bfb3a3888719cc09e900fa32452d414c04bbb7.
def localCycle00041 : Cycle where
  length := 11
  data := {
    node := ![.distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6]
    constant := ![-1, 0, -1, -2, -1, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 33 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0]

-- Cycle fingerprint 1b219c3de0d691d7d7b43f3f2517c023d68dce81f6f40394c3f243e2a8cedbaa.
def localCycle00042 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 23 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 1b4315f4a9f6d6f352fca5fa0cdb1e1462af6701c7d2249cd744a9226bb96d95.
def localCycle00043 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint 1bd3631e4834092549439070ab44f425a7be1650162f48d45dfa813ee1c213f1.
def localCycle00044 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![0, -1, -1, -1, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 2, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 23 0, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint 1ccd9a0ba815cf2714d88025b3b62c6affac4dbdf44cc5b0a5febf9689d7ce49.
def localCycle00045 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -2, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 1ce8b97bf62ba7e6778446674c7d01f7bd5ee9c641738e002ba86994aa556180.
def localCycle00046 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, -1, 0, -1, -2, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 1d7ed3ffb81cfd3a01c3c225581cd8a711f4296204a7e1d5021ecbb3c85bb64a.
def localCycle00047 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![0, -1, 0, 0, 3, -1, -1, -1, -2, -2]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 1ddc16d02d275322203b0baec0b16645b78b0220b12402c5f518b10d563fac23.
def localCycle00048 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 1e571df59e8e4d89bc579eda668ecf9e6540d24ae69710cbb1bdba723bcdc2bf.
def localCycle00049 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -3, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint 1e5acd1ac7047a529ca0bae852355c85f263538fa5445f2128a976749854c31c.
def localCycle00050 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4]
    constant := ![-3, 0, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0]

-- Cycle fingerprint 1ef7ec56d46fd0ac53344b7d55e8470adaa931561ac1f38bd2f949e10a799b23.
def localCycle00051 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 1f44573aa32a8dea428162ff58be8e2a1b9dc99cef20f32d8d4fab060fa775ac.
def localCycle00052 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 1ff5690296d98d2f501601b7f62b994a422aa35f33f3f8e27b9efbbe99a7ca8b.
def localCycle00053 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 0 5, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, -1, -1, 0, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapLower 5 2, .triangle 3 1, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 212707d1c4897ac7eb4fb713c4a1625a763075dae5002419feb11f9d46539bdb.
def localCycle00054 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 25 0, .triangle 26 2, .triangle 30 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 22989cd31e1b4b98987ac1c897f1a68648604908ec6c079cc3a3309fff8be402.
def localCycle00055 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 3, -1, 0, -3, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 23296c87f1613e5736ece29e36513eeb69431af9b56fa59e8e7aeac097c7a9d0.
def localCycle00056 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, 0, -2, -2, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 2]

-- Cycle fingerprint 23e55a5b68b41d16c50ce74166babf6bb5885e57fc52f1eb188f45e8ae957c65.
def localCycle00057 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 242df6340dcf79f2be5b87027d9a6e9460111bf56817378d3c4a5236e61e41f6.
def localCycle00058 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, 0, -1, -1, 0, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, true, false, false, true, true, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 9 2, .triangle 12 0, .triangle 22 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 24724d0d9356d585f5fa7f85b2da572f0b88ea142764497849c4855bfdbc12d9.
def localCycle00059 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 13 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 2554fcf0696b97e3717faa7ab2796e2a68c4068ac299705ff528ef2c44955071.
def localCycle00060 : Cycle where
  length := 9
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, -1, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 25f8199755a7f749c5583627089ec6f1792cf75986c2b102e862274a0541489a.
def localCycle00061 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 19 1, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 2624ad6435a3c50a7a53bdee14e8e91d1e28e8613483f16f8d47c486be55a22e.
def localCycle00062 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, 0, -1, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 265286f33e94e8d1084daa31fa5ef40991ba6de8e52eaf39d9d82c3f7e0f2190.
def localCycle00063 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, 0, -1, 3, 0, -1, -1, -2]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, false, false, true, false, false, false] }
  origin := ![.triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 2778d03374050d8e3e3de459157123f990e4f857fc42c979575df2b35a0d18d6.
def localCycle00064 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, 0, -1, -1, 0, -1, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 15 1]

-- Cycle fingerprint 27f1c8479c211fe596c733ab58c31f8475ed663325e6f2377f0bf88237fa7783.
def localCycle00065 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4]
    constant := ![-1, -1, 0, 0, -2, 0, 0, 0, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint 2a83f6f2ca57d9c0c8e49f5726f9e56d7d35816e84772edf142dddc8ac8ab838.
def localCycle00066 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![0, 0, -1, 3, -3, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint 2a99ecd236abb408ceac781c49a4ad2afb0eae4eea22ff1401efe7e35888ac8d.
def localCycle00067 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, 0, -1, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 2acb90070edb8b9960e59e808af694fd315f6b811149cbc9a1f896b0d64903d1.
def localCycle00068 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-3, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 32 1, .gapUpper 4 2]

-- Cycle fingerprint 2c26de0713c2ca5d4925038f24152e507500bcbda5d6666357a4cccf73c48e27.
def localCycle00069 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 34 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0]

-- Cycle fingerprint 2c5697454e728ce27c1c4f013d746a9bc53e8b848efc27ff50bcc74bff7171dc.
def localCycle00070 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, -1, 0, -2, 0, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint 2e3982b548ef7f7934643d13045c9d582adee9244be3860fc3f1bd88deace285.
def localCycle00071 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4]
    constant := ![-2, -2, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1]

-- Cycle fingerprint 2e5a7e1ac3db6a1317b9155f0906b86c04d4d9b85e58b2008df6876c7c057135.
def localCycle00072 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint 2e70c8418063a942d88de2691ea35355e3d5bc1959e3b1267a7828e1a5da1a8e.
def localCycle00073 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 2ef9b1d04c4770dbafec947d49c76e6d463221a7463615b7c3b1f60d45a0a891.
def localCycle00074 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint 303f639aaa116bcd5e0b2afa3b5ca53b35602e6b82b3da39e906d55480079ee3.
def localCycle00075 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, 0, -1, 1, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 3131cb570f9479d645af56e175f6c9cf643002fed89cb0655f7332cae98ee4a9.
def localCycle00076 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6]
    constant := ![0, -1, 0, 0, -2, 0, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0]

-- Cycle fingerprint 313b3554ee77f404cd87a655a4a11881a20287823073730c060a64ea943e99d2.
def localCycle00077 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![0, 3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint 3145bac4a4da9f06c39c281872cf2ec95aa8896bc9cf97b68579d0f05e39cd62.
def localCycle00078 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint 324c61adc1c903635ae9d0a82c66207120121939fa76b145e7ef2972f5b2f180.
def localCycle00079 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 2, -3, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true, true, true] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint 3299c5d4d5c46f9159d043ad5d6f42e79ca98c4f01cc018eaf61daa556d78b59.
def localCycle00080 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 338d23e6e9740c4d4c84973a1075bc555c6c392ba957cc391254fd6aaffd9928.
def localCycle00081 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1]

-- Cycle fingerprint 34ea97a320d7f34dd8542ee837f58497d91ea4d4f908925d6b62d4d8395278bc.
def localCycle00082 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 33 0, .triangle 10 0, .triangle 5 1]

-- Cycle fingerprint 355741cb5d23afd546d805f0b8a47c9a7d1aeee343c2a42698388788c0bb4ef1.
def localCycle00083 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 6, .distance 1 4, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 24 2, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 35ff52382767d3177829c93d30f0614b8776ed03b6c4191b2f5e3b2087f281a5.
def localCycle00084 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, -1, 0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint 36386197378625040ff3004088b886394321912a0a25a5a62b134d3f1d0e018d.
def localCycle00085 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6]
    constant := ![-2, 0, -2, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 19 1, .triangle 21 2]

-- Cycle fingerprint 364359bdca56063752587979ae8e8b66baa5f98995b802c3932514482da7a9ab.
def localCycle00086 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, -2, 0]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 18 1]

-- Cycle fingerprint 370728bd35eda36a700f60eccb5b8c2962c7270749d01a874b139b8ece9fe302.
def localCycle00087 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 377eb8db0a93e9f0f00be18957c8622933f33aa1f010224a8daae908dadaf7f6.
def localCycle00088 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 0, .triangle 9 1, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Cycle fingerprint 37bfc20a2818206058053221c1656b27060261a16480044ed55d35f91f1f04b6.
def localCycle00089 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 37cc5361e0a9c4f34f564d19a69ef3f6fe6d8c5f5a955f5424248cc330f02d6f.
def localCycle00090 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 2, .gapLower 1 4, .corridorLower 1 5, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 38db377f8f701f3a07ce495f993bc0b1a28fefea7c27bc21814c52986eb4b23b.
def localCycle00091 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 38e02d66ba3be761f7927c597ebb47351fe6a6659cccc42cf34f6d91da773baa.
def localCycle00092 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 3958f63d58e792604d59eb85683f22f37b74981f02499452201a6d257ba62c63.
def localCycle00093 : Cycle where
  length := 5
  data := {
    node := ![.distance 3 6, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![0, 2, 0, -2, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, true, false, true] }
  origin := ![.triangle 32 1, .gapUpper 4 2, .triangle 19 1, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint 396966649d3c92c7bbdf7d1903afdedad32f1c186402f65339e24c578bf19aa1.
def localCycle00094 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, 0, -1, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 3995928c98fd8b5862146b5ad5a7a797155161f82c921a0ffe70457416382237.
def localCycle00095 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![0, -3, 0, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint 399646632d7f063676108b448c80c6e552035b4f4935cabd8cc7eb339a978e12.
def localCycle00096 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 3 5, .distance 4 5, .distance 0 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, 0, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, true, false, true, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 33 0, .triangle 31 1, .triangle 12 0, .triangle 9 1, .triangle 5 1]

-- Cycle fingerprint 3a0a46d67be0670b4f5aa3d6f44f8f9f19ee78e8ae758ce9bc440d8f5a71da1b.
def localCycle00097 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 3a245c9eabdc136e4c91418de205d6a0bdf9ee7d15f65a01a268c33ac74b02a6.
def localCycle00098 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 5, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, false, true, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 5 2, .triangle 3 1, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 3abe8c8100ea5532b37d2f2e38019e02c96e490d89d0b3e058481bf101e3e20c.
def localCycle00099 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 3b018d5b0f2bcf1bd029038ea145032fe7aa6bab7036ff228701fc91fa03cfff.
def localCycle00100 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 3 5, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 33 0, .triangle 26 0, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 3bcbe135b7014c7e84b2a6d871aa5f757f085d89451b884d8a5a1db24d4bd61c.
def localCycle00101 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-3, 0, 0, 2, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 19 1, .triangle 15 1]

-- Cycle fingerprint 3c18901d4f5112342afe61e1620eb572eace3472819777c6f38a5105a578d5ec.
def localCycle00102 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 5, .distance 4 5]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 1, .gapLower 1 3, .triangle 22 1]

-- Cycle fingerprint 3f2ef9f0a7539d7f52f56ff96dfe3fa19bd064d91358622de05420b951dc202a.
def localCycle00103 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4]
    constant := ![-2, 0, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1]

-- Cycle fingerprint 3f72a8870255699e7b8e7e020bd4288cb07edc1e4cc3653cff28a1d78d77dff1.
def localCycle00104 : Cycle where
  length := 10
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, 0, -1, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint 40d61a7afef54a75a9b2d5c280cbfceab5ed9a42c6bb77f576af6b2e6ee341fa.
def localCycle00105 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, -1, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 42d70a4ffecabfa1c128d66d718a4da6bb7d315c737d83c73afbc6c36fb0af00.
def localCycle00106 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 31 0, .gapLower 3 3, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Cycle fingerprint 43693d2eb45f56d260df602a3aac3427812501db688235b55cd5e3e1f868bef9.
def localCycle00107 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, -1, -1, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 43fa92fbc82debeb29ac3bde3cf20767a518bbbaaf03362531ae5ee386a5bc3d.
def localCycle00108 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, -2, 3, -2, -1, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint 4502c2d72ed1a54bd68e623de9c1bb17533edd8ac96c346d29a46db262195cbc.
def localCycle00109 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, -2, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint 4517ac95d7bcab7b2d12bfaff8dc14daaab6f0212924ec45386263bf2ebf7c77.
def localCycle00110 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 45916ec02d2f3bc90ada47c71df493867f4e7520c6e84c16da6bfecab368e068.
def localCycle00111 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 46841c606e52ced529b870e553e61388634cad6ea1bf0caad97e458080c25f17.
def localCycle00112 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, 0, -2, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 46d1309cfe7c3446e8586c1bc8c745eb516923d056c17cd3068605d2346b518c.
def localCycle00113 : Cycle where
  length := 5
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .corridorLower 4 6]

-- Cycle fingerprint 48776341b4c65438d7559008ccd2577a03bd271ec81dbc075ddbed4e63b0a45f.
def localCycle00114 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2]
    constant := ![-3, 3, -1, 0, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 4893640ba90cc40959b43077b1e9e6c7031af4d77c459b3c842f185528bb370f.
def localCycle00115 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 6, .distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6]
    constant := ![0, -1, 0, 0, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, true, false, false, true, false] }
  origin := ![.triangle 33 1, .corridorLower 3 5, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 2 0, .triangle 19 1, .triangle 21 0]

-- Cycle fingerprint 4b1ef17974602b051cb141c1e26e29824871bcfc1e217e7430633614e6871468.
def localCycle00116 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -2, -1, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0]

-- Cycle fingerprint 4b6ff5946818c8e5db48bb9c0dc302ed605b8374d2856566150e6bf57f1f0994.
def localCycle00117 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint 4c14209e4c9e42382716dfdfab2bb3674d61320f449aeb37bf92cceade268c5f.
def localCycle00118 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 31 1, .triangle 9 0, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Cycle fingerprint 4c3bfc841962c90f386e5558285ee1e7b5ddb1db3c6b2c1d6b230d84f9594b55.
def localCycle00119 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, 0, -2]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint 4c5739d2c6847768d11402309f722ef45eafa639bbca291be23288dd5e61b056.
def localCycle00120 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 5, .distance 3 4]
    constant := ![-1, -2, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 31 0]

-- Cycle fingerprint 4c6787ae5ff45c71613e878f86b6425ab690dfc708300bddf8058a56c8c903fa.
def localCycle00121 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 6, .distance 1 6, .distance 1 5, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 0 6]
    constant := ![0, -3, 0, 3, 0, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, true, false] }
  origin := ![.triangle 4 1, .gapLower 1 4, .gapLower 5 0, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .gapLower 6 2]

-- Cycle fingerprint 4d1661038617402b2f228fa20e84262e6701cd94120f4fab24bc60115315c84c.
def localCycle00122 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 4db5812ecbfd81ddb44283c723ed786107dc5ca7db3ed80069a0f0aa36008637.
def localCycle00123 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6]
    constant := ![-3, 0, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 17 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 19 1, .triangle 21 2]

-- Cycle fingerprint 4ed91d0263873d79a160e3330ce64464c2ad1ed2dd0736536ed0e7e4bcb34c07.
def localCycle00124 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .distance 3 6, .distance 4 6, .theta 4]
    constant := ![3, -1, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 9 0, .triangle 11 0, .triangle 32 1, .corridorLower 4 6]

-- Cycle fingerprint 4ef08495795035b8631093e6a7bb01f9716b88d4f722e78ac2e1b3e476a93cdb.
def localCycle00125 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 2, -2, -1, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 32 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0]

-- Cycle fingerprint 4f3554cf69f4e359c05bbc3fad05c24878c3e030066e9481baf7fd9da0ecd63f.
def localCycle00126 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -1, 1, -1, -1, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 32 1, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0]

-- Cycle fingerprint 4fad6d8c6e3e593c5ee5f70b7f2ca4c5a28048cf50c8611f4defee85eddebd4e.
def localCycle00127 : Cycle where
  length := 8
  data := {
    node := ![.theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![0, 0, 0, 2, -2, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, false, true] }
  origin := ![.thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 50a0140179814941d1e3e209d2e93e0aef1648ef1388c34e5478f3c4284ca285.
def localCycle00128 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint 521b2b7336ad8464d83b6422f60f094d953e4f7c8af69f96fdd431062b3ecf6b.
def localCycle00129 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 2, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 0, .triangle 19 1, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 52515d53cd1e314d50830254f88966acf5a0a0469a8afc817beec53485a771fa.
def localCycle00130 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 52972b34356004d37b9dc0851b067db7e1460980bcefc26391a969549befeb0c.
def localCycle00131 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, -1, -2, -1, 0, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, true, false, false, false, true, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint 53ea8c6119f1a6e9518652dcba9539beeb3d39385c0988607fa7623d19fec855.
def localCycle00132 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, 0, -1, -1, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint 54a548c01dd81cdf698fe5106df2a8ddeead83f7853cfb1ba4503d116073d5fe.
def localCycle00133 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -3, 2]
    coefficient := ![0, 0, 0]
    strict := ![false, false, true] }
  origin := ![.gapLower 6 1, .gapLower 1 4, .gapUpper 5 1]

-- Cycle fingerprint 5620c003cd5ca6873a37fba58f8b7e96a43934da6e2df479f0bcc3631a52d29f.
def localCycle00134 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 4 5, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 31 1, .triangle 34 0, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 576b33136a46d4e6cd569f95071bc3688cc4edde2c5a82200a148a0ee6d77d69.
def localCycle00135 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, 0, -1, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 5794cc39360a7167603070caf1a046dbbecbb3fbb0fdcf130d2f78f39bc1a572.
def localCycle00136 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint 57e116fb4946ca29596ca8d61682c97d467cb6469828953cdc947a04a5ff70ad.
def localCycle00137 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 22 1]

-- Cycle fingerprint 5824a38ea53b7a44e05a8288e4a9067c11158cff2cab520c3557ac2fc9fc1134.
def localCycle00138 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-3, -1, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint 58957efe479f84ddc12667f2c18cc7ee81102a33cca4d1dbacc9c94872d25c33.
def localCycle00139 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 23 2, .triangle 24 1, .gapLower 1 3, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint 58cfdd84858c172bf5c64ef937373ae3bd16fdd5a3257337c535ac52eda6b784.
def localCycle00140 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![1, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 590c96b68fc21774d36167e9cd2a028b693f18e1beac4501830af3e2f227a33d.
def localCycle00141 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 2, .distance 2 3]
    constant := ![-1, -1, 0, -1, -3, 0, 0, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 2 0, .gapLower 2 6]

-- Cycle fingerprint 598293ca09f94b2798cf4db4f6e8b1ab33f327291be3d0dc3e34f5f7481b2273.
def localCycle00142 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint 5a28d79874061aa88c97bb8cfb69957fd192b0ba3bcd40830a8ac0da13553ac0.
def localCycle00143 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint 5adcbbb65e8a091ccd860ba19768c3f257d4ad2df45518cc8f8b08b493da7cc3.
def localCycle00144 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 3, -1, -1, 0, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapLower 5 1, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 5b6c10ac4ff5b7eb0a7eda347ef2397e5b8a66e86ca92620503d62438860778d.
def localCycle00145 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 6, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 19 1, .gapLower 1 3, .corridorLower 1 6, .gapLower 1 6, .triangle 2 0]

-- Cycle fingerprint 5b6fa368630f9f38476b4d41336cdaeee1aba9e76a4c3553f4f472bc7ae78ab3.
def localCycle00146 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 2 3]
    constant := ![-1, -1, 0, -1, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .triangle 26 0]

-- Cycle fingerprint 5b98ddfc98ef442a81a78cda18f579801a762c50da4daac9ea58bca87cf903e1.
def localCycle00147 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6]
    constant := ![-2, 0, -2, -1, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 5c96f37054b7bac940bc67395f93a0343906f24aef0015b313d6ef0038777f6e.
def localCycle00148 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 3, .corridorLower 1 4, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint 5d7c718573f66d0c974cbf5d5f57fe51706d0504c4d55141e89c3a4b06a083ec.
def localCycle00149 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .triangle 20 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 5f0630914e25465aeb0a7e600c8cf8da1bbdd813ec073265aa3e10c414feb712.
def localCycle00150 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false] }
  origin := ![.triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0]

-- Cycle fingerprint 623b440c8eb0e9409b112eaf9cc7652f22ea7a661945dc8976c16dcfb6140f77.
def localCycle00151 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 0 4, .distance 4 6, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5]
    constant := ![0, -1, -1, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 4 3, .triangle 13 0, .triangle 23 0, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0]

-- Cycle fingerprint 628cefb76f68662c44910cfd82114b171ac1656a7d67eeb9945d076886b07b1c.
def localCycle00152 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 2, .triangle 24 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 631c4daf1c050edff9e565f036a802e9b76e57b3227bbc7396cb37b0c287c4ee.
def localCycle00153 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, -2, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 63c587b48d96484e65b44e692b19818ae5830435f31f540c60dd7748ade52ab5.
def localCycle00154 : Cycle where
  length := 13
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, 0, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, true, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 24 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 63eec4f4d463da1ff593de6a3c9736336e4de752f562906d5d334c2711d6cfd8.
def localCycle00155 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -2, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .gapLower 3 0]

-- Cycle fingerprint 64f61d124f6de9e8d0f6a34c12a8af017f0944b03dab5d7e97ac653536a57a60.
def localCycle00156 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-3, 0, 0, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2]

-- Cycle fingerprint 65ac4da8dbcdfd7020b200bdea9780ebb81265fc1406cdfb20d898cfb028faf3.
def localCycle00157 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, -1, 0, -1, 3, -3, -1, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, false, false, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 6611dad06c4b40158e33579b04ad6a1f1a5234be736b17b51f12c9aff76f4cce.
def localCycle00158 : Cycle where
  length := 12
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 4 5, .distance 1 4]
    constant := ![0, 0, -2, 0, 0, 0, 3, -1, 0, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 9 2, .triangle 12 0, .triangle 22 0]

-- Cycle fingerprint 6a25538aa1bf4d7bac3f0ab5002a26352a2bdcad0000e8fd6701e6c806217ac5.
def localCycle00159 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, -1, -1, 0, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 6b62b906074e25d34e4e95069b87e9bc85cced252a64d29b6423b1c94deaac74.
def localCycle00160 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, true, false, true, false, false] }
  origin := ![.triangle 25 0, .triangle 32 0, .gapLower 6 2, .triangle 4 1, .gapLower 1 4, .triangle 20 1, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint 6ca81b38d1e831ec079b2ef634511710fc6e0e7caa264f69c1e8aabf0bc3a89b.
def localCycle00161 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 6da17ea09e8552b3ef4369340a2aa6ef1209a95f1d4488ed66489b5b618d6143.
def localCycle00162 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .gapLower 1 3, .triangle 20 1]

-- Cycle fingerprint 6eb890f5fbbf0cc81d97613b220173bc2f1022c3c6ae76169cb6d79a9d35cb24.
def localCycle00163 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 5 6]
    constant := ![0, -2, 2]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.triangle 24 2, .gapLower 1 4, .gapUpper 5 1]

-- Cycle fingerprint 6fe7796f422d42c700b3efa1734090130a09c148570d31fe2690a2f6d9295072.
def localCycle00164 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 21 0, .gapLower 3 0]

-- Cycle fingerprint 705367d3982d4cbe99383b7d75a9b849f5d1218e390b954b5fc3bbb7d05192ec.
def localCycle00165 : Cycle where
  length := 11
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 3 5, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3]
    constant := ![-1, 0, -1, -2, -1, 0, 0, 3, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, true, true, false] }
  origin := ![.triangle 25 0, .triangle 31 2, .triangle 20 0, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0]

-- Cycle fingerprint 71097c19433b6ce3f3872b0c196a83484db92e411413b6954a1829967339d594.
def localCycle00166 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![-2, 0, 0, -1, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 71205de578173ae6b1b8e911eefef38377829f01772457349c86c17638810c11.
def localCycle00167 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 29 0, .triangle 32 0, .triangle 9 2, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 71fd014da2d7af22be62a59d832fd75bd8883eef350bc29b7fbfff5c12bb561d.
def localCycle00168 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3]
    constant := ![-2, -2, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2]

-- Cycle fingerprint 7259d913abf72cf39e13ef91f091ddc0e73ba3cfbd4c0a36d2bd31fc9ebc02a4.
def localCycle00169 : Cycle where
  length := 3
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 6, .distance 5 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 5 1, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint 73753195de7419b491e9ae099bf4885fe126e34b78eed02a4a6bbf1d1f40e58b.
def localCycle00170 : Cycle where
  length := 7
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5]
    constant := ![3, 0, -1, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6]

-- Cycle fingerprint 73f3f6dcd818f2d513b755968b14e5f68331dc986cd7ecf0555019e7094a91ec.
def localCycle00171 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, -2, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 18 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 746d090476554ca0a738f88b70737f19f0f99c4b5437ccd9c9e9bbe411b93e01.
def localCycle00172 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 748cc575e84106c4f3d194188b35651d5775ab042b348bcc8dc6e01f616990a0.
def localCycle00173 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 5]
    constant := ![-1, 0, 0, 3, -1, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 0]

-- Cycle fingerprint 74b09af6a651a191978dd7862eb00b5c2fcffa93e21bd6888e950972ac3d637e.
def localCycle00174 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 5 6, .distance 2 5, .distance 2 3, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 33 0, .triangle 30 0, .gapLower 2 4, .triangle 25 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 74ddd34ff7af5625e9b5dc556ef8b903303c636bfe7d00c736e5e295ee619601.
def localCycle00175 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-2, 0, 0, 3, -1, 0, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .gapLower 5 1, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 74e152dcebba99fbc3187e7fb22538a8d929f274cfd0e00c9b53ae45d3502707.
def localCycle00176 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, 0, -1, 2, -2, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5]

-- Cycle fingerprint 75d4de5640580d0f7b579f397aa176262bb6c009488e2a3d6f50e94cdc382e26.
def localCycle00177 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 22 1, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint 75f0a3874836a5aeff6e4929f78940f446bcd4e9f164588815fc88b3126f12a7.
def localCycle00178 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![-1, -1, 0, 0, -2, -2, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, true, false, false, false, false] }
  origin := ![.triangle 25 0, .triangle 32 0, .triangle 23 2, .triangle 24 1, .gapLower 1 3, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint 766ed4c78e3a994f69ac590f4f9e85006dd5ad386e8787b3778f43dce687f400.
def localCycle00179 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, -1, 0, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .triangle 19 1, .corridorLower 1 3]

-- Cycle fingerprint 76b085941c0690b96a0c6b480b6d11e8adea9ee6df3f7652ae374e0a183c0d8d.
def localCycle00180 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, 0, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 76c633b4b9b2539c6c2919d0ae28e4a276b115cee7c6ee1745d4f6ea41d0d2d1.
def localCycle00181 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, -1, 1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 7722d66e873a2c3183ef4e302037b0263b733e123454d5711db8a8e9ae254069.
def localCycle00182 : Cycle where
  length := 7
  data := {
    node := ![.distance 3 6, .theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 3 6]
    constant := ![-1, 3, -1, -1, -1, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.corridorLower 3 6, .corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .gapLower 1 3, .triangle 21 0]

-- Cycle fingerprint 77236d6af1163e1ea58535534ce07fdfffee09cfbbbe836934b4f508a6e1fcbc.
def localCycle00183 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-2, 0, 0, 2, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 17 1]

-- Cycle fingerprint 77b5fac0a59e2d49dd95fbd5b2bbb501cfb98722f97177e21c4b12ee947e8634.
def localCycle00184 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 77ca3b2b6d0cfc7d5217fdee0c02346ac835ede9be684ff260dd2a9ebac8dc12.
def localCycle00185 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint 77d9af45a62caf09fb1f1d0c7d1ae39f16f1a0eb029697edac7297d515396df7.
def localCycle00186 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 0 4, .distance 4 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 9 2, .triangle 12 0, .triangle 34 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 78a1dfba09fd3eee46fbd32e14b7688d8f58a1a8b79efd960caf34bebc658c9f.
def localCycle00187 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -2, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 19 1, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint 790386d7ba9c7627aec58155605a3bb066b0e2f7fa5d083263b89582019e64e1.
def localCycle00188 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, 0, -1, -1, -2, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 7a599a3c8311138c10d39ace607bfd4f1c70996723136750febcec32882724cb.
def localCycle00189 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, -2, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint 7a97380a18b2db7726c182c42d9ab0f8803b841a4056016c8fcddf0a07ab89a6.
def localCycle00190 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6, .distance 1 6]
    constant := ![0, -2, 0, -2, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, true, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint 7b2011fa748549f54ab8630f02abf00b1e2fce5a727b6635e9ff9a19fb0b57c0.
def localCycle00191 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .triangle 21 1]

-- Cycle fingerprint 7b3d5328c975bc616eb90a817dec4e196f87121d0316b8d09fc4ba80d2901483.
def localCycle00192 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6]
    constant := ![0, -2, 0, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.gapLower 6 1, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0]

-- Cycle fingerprint 7ca2085038f1b680520504c2a96d08578279b0d331faf27e01596a6b6f2859e3.
def localCycle00193 : Cycle where
  length := 9
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 0 5, .distance 5 6, .distance 3 6, .distance 1 3, .distance 3 5, .distance 4 5, .theta 4]
    constant := ![3, -1, 0, -1, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, true, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 2, .triangle 14 0, .triangle 33 2, .triangle 21 0, .triangle 20 0, .triangle 31 1, .corridorLower 4 5]

-- Cycle fingerprint 7d2a19cbb47ed4982bf8a488f8fb0a6d5425b14d61a509dfa215ff7aa6fe1e16.
def localCycle00194 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -3, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint 7d32b45e7ecbb4c5fbae8abdda823192fff79887de8d515cb08f6825eb7473cb.
def localCycle00195 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, true, false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint 7d90434e169ecbd8aff14e85f627eb44eb6f938aaf2b704e1cecc5b4c303b6bb.
def localCycle00196 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 7eca13975cc9c4ec2c9feb16bab36f1087895029daa1defa3e693edd47f05b2e.
def localCycle00197 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 7f658e6af0c2626560bcedbd688d897a1dd9ef2cb81c757d9b7e121fdcf030a2.
def localCycle00198 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, -1, -2, -2, 0, -1, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint 7fbd5a6331cd97648ac853f14c3ad8e472d423f65a29ccc2ac679912b711e975.
def localCycle00199 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 0 5]
    constant := ![0, -3, 0, 0, 3, -1, -1, 0, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 3 1, .gapLower 1 3, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .gapLower 5 2]

-- Cycle fingerprint 7fe95e0602ae8fa135f40257a94387ab78377d50553faca0c10d5ae824c510a7.
def localCycle00200 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 0 6, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, 0, 0, -2, 0, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .gapLower 6 2, .triangle 4 1, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint 80a7976cd090a254d5fd9642082c58933985bad57c6263f057b3fab02fcef0a7.
def localCycle00201 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![0, 0, 2, -3, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 80fd53f2ec879655dd47ac98b7d7153e0bc6c3038669452635606b4ee547e701.
def localCycle00202 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![-1, -1, -1, 0, 0, -2, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, false, true, false, false, false, false, false] }
  origin := ![.triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint 81427d2c78f03357e25cb8b2c043c7a1e3b435cde1d8656cc1b5fb9f6de8aae7.
def localCycle00203 : Cycle where
  length := 3
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .theta 1]
    constant := ![3, -3, -1]
    coefficient := ![1, 0, 0]
    strict := ![false, false, false] }
  origin := ![.corridorUpper 0 1, .gapLower 1 5, .corridorLower 1 4]

-- Cycle fingerprint 84817e718f1b6ad422ff351542a4f4ccee51c78935d4c35255cea623c08e64b5.
def localCycle00204 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![-2, 0, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, true, false, false, false] }
  origin := ![.gapLower 1 4, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 84a6f82e2c5f1dbc6892ac91a536738d59c02c20fce3deb55b9f615280050e51.
def localCycle00205 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 23 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint 85b4190868325e7b091e8c9f6d7d86419c5996d3d32921365ccc2f4516e0aa99.
def localCycle00206 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -2, -2, -1, 4]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, true, false, false, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6]

-- Cycle fingerprint 867d57b840c516a54c5f8edb9a25cbf7b63154a5ee04cf129133712b16326edd.
def localCycle00207 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![0, 0, 3, -1, -1, -1, 0, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 86cfa28ac3b35ca96e8d6899c6160f9005e4bf165f1e793fbfc66c2068b8d41a.
def localCycle00208 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 0, 0, 3, -1, 0, -1, -1, -2, 0]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint 876b495898da0aee2667ebb8d9211a01d6fe1b6488556d6d590a4fcfb4c27ba6.
def localCycle00209 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 20 1]

-- Cycle fingerprint 87aeb4ccdf974c8d1870efaa522f70306f0e52646745aac55714214622b36f34.
def localCycle00210 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, 0, 0, -2, 0, -2, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, true, false, true, false, false, false, false, true, false] }
  origin := ![.triangle 27 0, .triangle 32 1, .gapLower 4 2, .triangle 2 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint 884badf767322ce7cdaa61abd400d34356b9ace7f7b39f24fc2270dbea38bf4f.
def localCycle00211 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6]
    constant := ![-2, 0, 0, -2, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2]

-- Cycle fingerprint 88732b3a39206ae93713e3fd9dc14b0dec47cab0f9c4a8d535f7590ee332cb2e.
def localCycle00212 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -3, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 8875a025ad420c8302a44f222defcca71d37c6e4880469e59a539ac79736eca9.
def localCycle00213 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 4]
    constant := ![0, -2, -2, -1, 0, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, true, false, false, true, true] }
  origin := ![.triangle 22 2, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1]

-- Cycle fingerprint 8880090a011db507eaa7f4b1fbcfe3f90d63838000df9de17736a75c88400865.
def localCycle00214 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .gapLower 1 4, .corridorLower 1 5]

-- Cycle fingerprint 889537d16cce45da18aef7a83fb5a50817b2712ba89764d43bddd451b864ca7f.
def localCycle00215 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 5 6, .distance 0 5, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 14 0, .corridorLower 0 5, .thetaLower 0]

-- Cycle fingerprint 88c143d1e44918ee16d1d715e57a35a65427237089fdf032f2c6f8d3852aee75.
def localCycle00216 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 5, .distance 5 6, .theta 5, .theta 4, .theta 3]
    constant := ![3, -1, -1, 0, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 12 2, .triangle 14 0, .corridorLower 5 6, .thetaNext 4, .thetaNext 3]

-- Cycle fingerprint 89b7fccacd29916c318f2495e401a00c7c668188114cf853f96143bfbc586e38.
def localCycle00217 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint 8b9c184d6a130831dce2904b50e5e2d332a7d0344cbff9bfa19e4f6766349b77.
def localCycle00218 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-3, 0, -1, 3, -1, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2, .triangle 24 1]

-- Cycle fingerprint 8c25530d378da2596e7c732930e6335feb8c73c05911c36eca6e643c28e04ce5.
def localCycle00219 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, -2, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 22 1, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint 8cb95db2f9d934e8fdd429ada131a1bfd99c6a4c1ffdc7f028e163cd2748dace.
def localCycle00220 : Cycle where
  length := 3
  data := {
    node := ![.distance 1 6, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![-1, 2, -2]
    coefficient := ![0, 1, 0]
    strict := ![false, false, false] }
  origin := ![.corridorLower 1 6, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint 8cdbc07bde3bfa3bdbd4049a6c2b28f58c7764288eaf6b5d2856b737287dea13.
def localCycle00221 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 4, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 2, .triangle 28 0, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint 8ceb54ad28dbcf3a26057101d111ec29d6597fdfbc75fca532758b5b124a0e9c.
def localCycle00222 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, -1, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 8d39372ad21de445e74e1b9288cf4203101f15223aadb26cbf41dc63d9c352ec.
def localCycle00223 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint 8d852e9b2a1d1736695a70fc11046e11cff5bd61c6b6335f86247f3a58d8f5c9.
def localCycle00224 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6]
    constant := ![0, -1, 0, -2, 2, -1, -1, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, true, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 32 1, .triangle 19 0, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0]

-- Cycle fingerprint 8dff5b13f82277508c3c1e185dc0d2b654ee488ca92f95599bf838c7bdb097f0.
def localCycle00225 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .triangle 22 1, .gapLower 1 2, .gapLower 3 0]

-- Cycle fingerprint 8f0fd2c980d5774da555a8cd173eb8d697cb39d4806f2fe2484494e36c356af2.
def localCycle00226 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -1, 0, 0, -2]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, false] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 19 1, .triangle 21 2, .gapLower 1 2]

-- Cycle fingerprint 8fff767ca2c36ee88dcb897079da5497f078e69b31e54595c7eca599d40bb434.
def localCycle00227 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint 90b71747b3907efa42dc35f5d8b40bcc46cec9b310deab3097205c3be8f4ad42.
def localCycle00228 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .theta 0, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1]
    constant := ![0, 0, 0, 2, -2, 0, -2, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0, 0]
    strict := ![true, false, false, true, false, true, false, false] }
  origin := ![.thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .triangle 22 2, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint 90ed888ccd250b539b66a663bdedb717d535fb7505cbb62ebb9984e01afe255a.
def localCycle00229 : Cycle where
  length := 7
  data := {
    node := ![.theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6, .theta 5, .theta 4]
    constant := ![3, -1, -1, -1, 0, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1, .corridorLower 5 6, .thetaNext 4]

-- Cycle fingerprint 910c8821abf84f774fe8945bd2edb2d6029c71d424e4eae5afbe9881c6ff2857.
def localCycle00230 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5]
    constant := ![-3, 0, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0]

-- Cycle fingerprint 91172f5cedce585f9bd524174411c8952549ef8d3d240d577d9171a07b64f984.
def localCycle00231 : Cycle where
  length := 9
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0]
    strict := ![true, false, false, false, false, true, false, false, false] }
  origin := ![.triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0]

-- Cycle fingerprint 93414166f86daeaa195e2342a4abaae1d4da762fe8b0629be8ad4b6c89e39027.
def localCycle00232 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![0, 0, -2, -1, 2, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 938efa9cd2c4130c5fbac5be372a610ef7d1e3b8f5274141ba466223cf408213.
def localCycle00233 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -3, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint 93d77d829953fd4edb0af15b1dc005272bf1bd929c478568b38fe53db65ee386.
def localCycle00234 : Cycle where
  length := 10
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 9487d4bb40d088e64deba350a5d06decf7432175a9dadbef3f8e6ca962135bd9.
def localCycle00235 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3]
    constant := ![-1, 0, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 2, .gapLower 1 3, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3]

-- Cycle fingerprint 949776173082decf9a4940d543049b7218b249262afbbaca923f542b5c350212.
def localCycle00236 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, -1, 0, 0, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint 94d209a5d574d11cd8c87180527594a7b8abf7f60b7ff5a7ef2983a895586155.
def localCycle00237 : Cycle where
  length := 10
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, -1, -1, -1, 0, 0, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, true, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint 9501be82bdcb9fd7efaabd98f78e3c00cc9ee2e57cf248fd76a12bc7314f9e1f.
def localCycle00238 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -2, -2, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint 980c9e94e7561fb9d5cfee0c50f87176e4d3cc594cb36cb1d6eeb7d4452a7fe4.
def localCycle00239 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint 98e07c01b5a0605a635912a221fbec5fd6b4a83c3589cdc46fae2388b177a1a2.
def localCycle00240 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-3, -1, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 19 1]

-- Cycle fingerprint 99dc52f425147544b86cb5c5dfdcec6c997616b26ab64c4111a2ec1f87bb5ec0.
def localCycle00241 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint 9a47d1d14ab3364074d37fb7d1c5a8640795c9be0a8689fa31bdd39c6a2c2ca2.
def localCycle00242 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 3 6, .distance 2 3, .distance 3 4, .distance 4 5, .distance 0 4, .theta 0, .zero]
    constant := ![0, 3, 0, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 32 2, .triangle 27 0, .triangle 25 0, .triangle 31 0, .triangle 12 0, .corridorLower 0 4, .thetaLower 0]

-- Cycle fingerprint 9b238f608bb8782490042f43757565a380d623d44c8ff7950f393566663c6d2b.
def localCycle00243 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 0 4]
    constant := ![-1, 0, -2, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, true, false, false, false, true] }
  origin := ![.triangle 13 0, .triangle 23 2, .gapLower 1 4, .corridorLower 1 5, .gapLower 1 6, .triangle 2 2]

-- Cycle fingerprint 9e5d3f9eb9c9bafc73993f979befc5fd584028548dc55c604550d1c48e1d48a3.
def localCycle00244 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5]
    constant := ![-2, -2, -1, 4, 0, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0]

-- Cycle fingerprint 9f9480fe89badf93b569802ef68e40d5ff3e7b765d70e7e53350086dcca0e568.
def localCycle00245 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -3, -1, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint a0347d7590f5f79e9fd4ee0ddf663ce6097bbaca796bf936fe98f911e47d8cad.
def localCycle00246 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, -1, 0, 0, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0]

-- Cycle fingerprint a085cfe425f3c0f3d0d22567f0bbae22aba2ae7ce4cdbd726f099c63baddee64.
def localCycle00247 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 2, 0, -3, -1]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint a1cd999522dc380a527b8e767839cdc343cfb7bfd6c6d9f917546034f5af22f9.
def localCycle00248 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-2, 0, 0, -2, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 20 1, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2]

-- Cycle fingerprint a225bc60687bc42b8851cc219f81e13734948ed6140a97d9db3ad0c5c88efeb4.
def localCycle00249 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2]
    constant := ![-3, 3, 0, -1, -1, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1]

-- Cycle fingerprint a2601035bd31534f712076e0fa64b3538d32bf8ecf36befeb4c15c5b7709a115.
def localCycle00250 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 2, -2, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint a371546670f34f9e521ddc2b1808986277d9e2981232f513114905d8bb44d01e.
def localCycle00251 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 3]
    constant := ![3, 0, -1, -1, 0, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .triangle 31 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 3]

-- Cycle fingerprint a3d6336a8e49145f9dab1108ca5fe78083e8b9d74a9246b73bfdbc6a65e04e41.
def localCycle00252 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 6]
    constant := ![-2, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 20 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 2]

-- Cycle fingerprint a60cd12cd743aef8de2ec425d0740547afa2664fba993742bacef1c28e9e3c67.
def localCycle00253 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 4, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 4, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint a628240ae8af62335c399bf04c11974af944353056afbc98d69746c17c211c67.
def localCycle00254 : Cycle where
  length := 8
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6, .distance 1 5, .theta 1, .zero, .theta 3]
    constant := ![3, -1, -1, 0, -3, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .gapLower 6 1, .gapLower 1 4, .corridorLower 1 5, .thetaLower 1, .thetaUpper 3]

-- Cycle fingerprint a64495e296251a072763f4d2f2c484ffc4afd2f2331306c7d4ef258cc01261f4.
def localCycle00255 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 4, .distance 4 6, .distance 0 4, .distance 0 3, .distance 0 2, .distance 2 6, .theta 6, .theta 5, .theta 4, .distance 2 4, .distance 4 5]
    constant := ![-1, -1, -1, 0, 0, 2, -2, 0, 0, 3, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, -1, 0, 0, 1, 0]
    strict := ![false, false, false, false, true, true, true, true, true, false, false] }
  origin := ![.triangle 31 0, .triangle 32 0, .triangle 13 0, .gapLower 0 2, .triangle 5 1, .gapUpper 2 2, .gapUpper 6 6, .thetaNext 5, .thetaNext 4, .corridorUpper 2 4, .triangle 28 0]

-- Cycle fingerprint a6cccf0b538710c98e974ab3475d3726aa63ebfe27a56bcbddce72ef1862d151.
def localCycle00256 : Cycle where
  length := 9
  data := {
    node := ![.distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 4, .distance 4 6]
    constant := ![-1, 0, -1, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 32 0, .gapLower 4 3, .triangle 12 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 2, .triangle 29 0]

-- Cycle fingerprint a7569e9f0fec3b5aa437598822cbe231414d80ce384596fe689b294c8e5d9179.
def localCycle00257 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, 0, -2, 0, -2, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, true, false, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .gapLower 6 1, .gapLower 1 4, .triangle 17 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 5]

-- Cycle fingerprint a7717b5808e46c8522d0db6b999a18118faa4243cd10cb22abdec81fa731d002.
def localCycle00258 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-3, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint a799b8a8d4d4cf079c2c64a9bc190d4d07c8503d341b3bf94129f828996d4062.
def localCycle00259 : Cycle where
  length := 6
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, -1, 0, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint a8daeceb860541ced2933832ba26f65bb42b012698b0776cd64fe1685e6b5c2d.
def localCycle00260 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, false, true] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 2 0, .triangle 23 0, .triangle 34 1]

-- Cycle fingerprint aa1d454fa3ca329c60dfcf2feeff6250ba04d1f251e78d3839de6773824f3ce8.
def localCycle00261 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint aaf632a2e25ce1df4c7a1197927961a7dbf843df86f23f92e4874b86f403fb68.
def localCycle00262 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 19 1, .triangle 21 2, .triangle 24 1, .triangle 17 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint ab5275811d89aa03bed341a4ed1d96f2538db7d77059d81adc7088538e523927.
def localCycle00263 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![3, 0, -1, -1, -2, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, true, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0]

-- Cycle fingerprint ad3f8471895a31e3246c58640a9d2258da1c4345598a1b61db79a0f80ad969b4.
def localCycle00264 : Cycle where
  length := 8
  data := {
    node := ![.theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6]
    constant := ![2, 0, 0, 0, -2, -2, 0, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.gapUpper 6 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6]

-- Cycle fingerprint ade14e33c54e5c964bd6ccacd2bda9d4c65cc22f3ea13bcd0bdca38272de4a83.
def localCycle00265 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, 0, -1, 1, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5]

-- Cycle fingerprint ae57e7d3b1b29345d7d1f8f14dcb2546d1a4ef917412898c190081a2cc3cd40a.
def localCycle00266 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -3, 0, 0, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, true, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint aea160388e0708886dba262811aa62af5836dd5c4cfb574f0c61407e19c723d2.
def localCycle00267 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, 0, -1, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint aea394be546750fc51638bbf37ce9fcc459ff26303e9a69302ea96594679fa8a.
def localCycle00268 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4]
    constant := ![-3, 0, 3, -1, 0, -1, -1]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false] }
  origin := ![.gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0]

-- Cycle fingerprint af19982e99428b5d61a5c9540de55babe35f0d8602fe98dfb0003811cb86e62f.
def localCycle00269 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![-3, 0, 0, -1, 3, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, true, false, false, false, true] }
  origin := ![.gapLower 1 3, .triangle 20 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 23 2]

-- Cycle fingerprint b097eb62f69455073f6cfeef59d820d3599ee516486c024c501b0e4a25aa3b50.
def localCycle00270 : Cycle where
  length := 8
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4]
    constant := ![-2, 0, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, false, false, true, false, false, false] }
  origin := ![.gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3]

-- Cycle fingerprint b161542881b04bba5172c6f2617cb080ba2e78766c471998ac121aa2ceb2585f.
def localCycle00271 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 4 6, .distance 3 4, .distance 4 5, .distance 0 4, .distance 0 2]
    constant := ![2, 0, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0]
    strict := ![true, true, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 34 2, .triangle 32 0, .triangle 31 0, .triangle 12 0, .triangle 6 1]

-- Cycle fingerprint b2063153ea98dbc718beebc9c76dcaa4ef63bc0dbb922e5a4e051602660b5c02.
def localCycle00272 : Cycle where
  length := 9
  data := {
    node := ![.distance 0 5, .distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 0 5]
    constant := ![0, -3, 0, 0, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![true, false, true, false, false, true, false, false, false] }
  origin := ![.triangle 3 1, .gapLower 1 3, .triangle 19 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 5 2]

-- Cycle fingerprint b2735907baf1d33412a0597b9699c8e2731710cc20090e513c88c15a23424443.
def localCycle00273 : Cycle where
  length := 8
  data := {
    node := ![.distance 5 6, .distance 4 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6]
    constant := ![-1, -1, -1, 0, -3, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![false, false, false, true, false, false, false, false] }
  origin := ![.triangle 34 0, .triangle 31 0, .triangle 19 0, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6]

-- Cycle fingerprint b2de7d27b2adcbd3e4243ee68b87e712a3491277cac85cd0ed627d453c55359f.
def localCycle00274 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 24 1, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint b40260e8584057cfd7e9b32040009e57fb9dfa7793a3518936106859a11ddd70.
def localCycle00275 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint b41c9f2f7190fff768aed4e6eb44d93b8c93837c037c9ca8dcaac5956e475029.
def localCycle00276 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, 0, -1, 0, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, false, true, false, false] }
  origin := ![.thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint b48b630d2c4275f32dd166a29588824a614ccc2f16cb6c59e73436268b3d767f.
def localCycle00277 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .theta 0, .zero, .theta 6, .distance 1 6]
    constant := ![-2, -2, -1, 0, 0, 0, 2]
    coefficient := ![0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .thetaNext 0, .thetaLower 0, .thetaUpper 6, .gapUpper 6 0]

-- Cycle fingerprint b494585c15fa3b0c9a6e18a300ae83fad2370415d325401b354b5ff4c793c017.
def localCycle00278 : Cycle where
  length := 4
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .theta 1]
    constant := ![2, -1, -2, -1]
    coefficient := ![1, 0, 0, 0]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .gapLower 1 4, .corridorLower 1 6]

-- Cycle fingerprint b51aee9f00dab80fd0d2e438aaf2d38e019c6601795cccd47fac4c201fbce393.
def localCycle00279 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5]
    constant := ![-1, 0, -2, -1, 2, 0, -1, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false, true] }
  origin := ![.triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1]

-- Cycle fingerprint b59ede5762bd0f63240528a4a41b7dd6e2a4ebe3d2ac0b50445aa93849281e6c.
def localCycle00280 : Cycle where
  length := 8
  data := {
    node := ![.theta 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5]
    constant := ![0, 0, 0, 0, 1, -1, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, true, true, true, false, false, false, false] }
  origin := ![.thetaNext 4, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6]

-- Cycle fingerprint b64b0b1142dd462931546e9b2dfcafccd3a2c79392ac8fd105b73b67f5dc9f0d.
def localCycle00281 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4]
    constant := ![-1, 0, -1, 3, -3, -1, -1, 3, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, true, false, false, true] }
  origin := ![.triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1]

-- Cycle fingerprint b752d76002ed8fe19e442173ecb7a5a0481d76ada9ded57c26012ffe1cc1618e.
def localCycle00282 : Cycle where
  length := 12
  data := {
    node := ![.distance 2 3, .distance 3 6, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3]
    constant := ![-1, 0, -1, 0, -2, -2, -1, 0, 0, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, true, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.triangle 27 0, .triangle 33 1, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0]

-- Cycle fingerprint b8a592fcf342df81f659bf20b52197d6e4f8c4392f4ddc7542198c146a5e6865.
def localCycle00283 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 1 4, .distance 4 6, .theta 4, .theta 3]
    constant := ![3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 22 0, .triangle 23 0, .corridorLower 4 6, .thetaNext 3]

-- Cycle fingerprint b9155bf81c90147505f28386086aac00802caebfd937c239cd2efd4b285bf806.
def localCycle00284 : Cycle where
  length := 11
  data := {
    node := ![.distance 1 3, .theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 3 4, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3]
    constant := ![0, 3, 0, 0, -1, 0, -1, 0, -1, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false, false, false, false] }
  origin := ![.gapLower 3 0, .corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 32 0, .gapLower 4 3, .triangle 12 0, .triangle 22 0, .gapLower 1 2]

-- Cycle fingerprint badd4853d95c127d6ddfdc8c4c71bb573c61f0d9d8d6236f9d9c121a7cd9a45d.
def localCycle00285 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5]
    constant := ![-2, 0, -2, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, true, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1]

-- Cycle fingerprint bc1587ac4c5e5e45ec1fae000c52400227cc5bd45e05090f2aef1bda8b5aedec.
def localCycle00286 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .gapLower 1 2, .triangle 15 1]

-- Cycle fingerprint bc39f7065882215d12d48f0d0bcc5d12aaad7957cf6f45937f568ec85af3efd2.
def localCycle00287 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -1, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .triangle 24 1]

-- Cycle fingerprint bcd41bfc1a77982edf587fc5372559d3a89e6c54d605a186343c87a83bd00f00.
def localCycle00288 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 1 6, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, -1, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 23 2, .triangle 24 1, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint bdfb70cac395f95f7b0357ca160fa93a0d97fd1c16d2b4d8696f354fac1db0a7.
def localCycle00289 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 5, .corridorUpper 0 1, .triangle 2 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint be7ff360ca7373eeaac6cfb6af0d80ecdb7e404c0647ae09469d0bc58222bcfb.
def localCycle00290 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5]
    constant := ![-2, -2, 0, 3, -1, -1, -1]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .gapLower 3 0, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0]

-- Cycle fingerprint bfc6fc64172711851382755d45c7160fa6799fd66a9763cbd03b1d2525a6651d.
def localCycle00291 : Cycle where
  length := 11
  data := {
    node := ![.distance 0 3, .distance 0 2, .theta 0, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 0 3]
    constant := ![0, -1, 0, 0, 3, -1, 0, -1, -1, 0, -1]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true, false] }
  origin := ![.gapLower 0 1, .corridorLower 0 2, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .gapLower 6 4, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 9 0]

-- Cycle fingerprint c04520de512da7e52e5543aeaa5de93db5f646450e926ca4ebe1e89108f9d7fc.
def localCycle00292 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 4 5]
    constant := ![-1, 0, 0, 0, 1, -1, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, true, true, false, false, true, false] }
  origin := ![.corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .triangle 4 0, .triangle 23 1, .triangle 22 0]

-- Cycle fingerprint c10f87a4001262306045314d46c5d8c79d0dc008eec594d6ad48dc6aca0fe0d2.
def localCycle00293 : Cycle where
  length := 11
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 0 3, .distance 3 6, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, -1, 0, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 10 0, .triangle 11 0, .triangle 33 1, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint c114c5993b8d39e7dc4a23aab2dab86c971e61cd9702c9ba13362daaf8401b32.
def localCycle00294 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6]
    constant := ![0, -2, 0, 0, 0, -2, 3, 0, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, true, true, false, false, true, false] }
  origin := ![.triangle 24 2, .gapLower 1 4, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1, .triangle 3 2, .triangle 14 0]

-- Cycle fingerprint c150b2bd16b179131cfc8e986979c2fada0851887601906fee6b029ddecce5b1.
def localCycle00295 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 2, 0, -2, 0, -2, -1]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .gapLower 1 3, .triangle 20 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint c17fc968c676933d438bcd9905ecfd9b1bca1485dfd1eb8f3d26b7cb2f3ffeae.
def localCycle00296 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, -1, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2]

-- Cycle fingerprint c19c4b338475fe63b243dd8d7a0c645754cf4317ac3c4be8f499dc9d3c9be794.
def localCycle00297 : Cycle where
  length := 8
  data := {
    node := ![.distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5]
    constant := ![-1, 0, -2, -1, 2, 0, 0, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false, true, true, false] }
  origin := ![.triangle 22 0, .gapLower 1 2, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0]

-- Cycle fingerprint c208651bbd966d202daa475f4ea58bebf29b2c7985272744d50ac9a7b69eedac.
def localCycle00298 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .distance 2 3, .distance 3 6, .distance 5 6, .distance 1 6, .distance 1 5, .theta 5, .distance 4 5, .distance 3 5]
    constant := ![-1, -1, 0, 0, -2, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.triangle 26 0, .triangle 27 0, .triangle 33 1, .triangle 24 2, .gapLower 1 4, .gapLower 5 0, .corridorUpper 4 5, .triangle 31 2]

-- Cycle fingerprint c27512d80ebd0e24954f2b92338b708ae4a5b86e732fddc6fc4a79121f134ce7.
def localCycle00299 : Cycle where
  length := 3
  data := {
    node := ![.distance 3 6, .distance 1 3, .distance 1 6, .distance 3 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 3 2, .gapLower 1 3, .triangle 21 1]

-- Cycle fingerprint c31fb1f797164aac41011d359ea0dcd3d3b35a5d6cc432133edef290857b6fbb.
def localCycle00300 : Cycle where
  length := 12
  data := {
    node := ![.distance 5 6, .distance 0 5, .distance 0 4, .distance 0 2, .distance 2 6, .theta 6, .theta 5, .theta 4, .distance 2 4, .distance 4 5, .distance 3 4, .distance 4 6, .distance 5 6]
    constant := ![-1, 0, 0, 2, -2, 0, 0, 3, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, true, false, false, false, false, true] }
  origin := ![.triangle 14 0, .gapLower 0 3, .triangle 6 1, .gapUpper 2 2, .gapUpper 6 6, .thetaNext 5, .thetaNext 4, .corridorUpper 2 4, .triangle 28 0, .triangle 31 0, .triangle 32 0, .triangle 34 1]

-- Cycle fingerprint c3b0127ddbb4ee204db850540190af616dcb35f2d199a370bd6fd8839075be7a.
def localCycle00301 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4]
    constant := ![-3, -1, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 22 1]

-- Cycle fingerprint c3eb8d9c954f177e4e5a803f6c27321c67356d924bd62b6b42ef9fcb04e30e8f.
def localCycle00302 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-1, 0, 0, 0, -3, 3]
    coefficient := ![0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, false, false] }
  origin := ![.triangle 3 0, .triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint c3fa3266719f43e263b7de315dc4f416a99ae669ceb0542dbd01c8d611377196.
def localCycle00303 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-1, 3, -1, 0, -2, -2]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 3, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .gapLower 1 2]

-- Cycle fingerprint c467cf3197c3a04d0ae15df4377e3325f4244c3337c8fd6ac6b3137b34f1896f.
def localCycle00304 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2]
    constant := ![-3, 3, -1, 0, 0, 0, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, true, true, false] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 19 1, .triangle 21 2, .triangle 24 1, .gapLower 1 1]

-- Cycle fingerprint c49e129a89d2f181b22a7d24b1968f2a9bd70b9454910ea98e725955c0da5706.
def localCycle00305 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 5, .distance 5 6, .distance 1 5, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, -1, -1, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, true, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 0, .triangle 34 0, .triangle 24 0, .triangle 20 1, .gapLower 3 0]

-- Cycle fingerprint c68dda9c0f6cd773210015ee5f48301c1b5eeff26f507c8bbd7ca9d32bd1e59c.
def localCycle00306 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, 0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, false, false, false, false] }
  origin := ![.triangle 23 1, .triangle 22 2, .gapLower 1 2, .corridorLower 1 3, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint c6c4da7dbb19e254736e537b1ff23b87d2dcdd26426c8f9913d06cdd076c1d9d.
def localCycle00307 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 2 4, .distance 4 6, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 28 0, .triangle 29 0, .triangle 32 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c76fab4beab994c4eeb57aed81202df5b2a834fc80188bbd95bc1a682ae4fddd.
def localCycle00308 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint c82196962e58d7c4e8564dc9ba61bf0195644410e98433a770a1ec47fb670a77.
def localCycle00309 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 4, .distance 1 6]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 24 1, .gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 2]

-- Cycle fingerprint c8493ca2639fd68c5c0b993d13fc85931f7fd36a1257caf16fe71442d721f8d9.
def localCycle00310 : Cycle where
  length := 9
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 6, .distance 2 4, .distance 4 5, .distance 3 4, .distance 0 3, .theta 0, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 2, .triangle 29 0, .triangle 28 0, .triangle 31 0, .triangle 9 0, .corridorLower 0 3, .thetaLower 0]

-- Cycle fingerprint c8a166698caadc001b87995bc5fc456fc31d5b5abed377d831fbbe8d3cf5b4cd.
def localCycle00311 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .distance 1 2]
    constant := ![-1, 0, 0, 3, -1, -1, 0, -1, -2, -2]
    coefficient := ![0, 0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, true, false, false, false] }
  origin := ![.corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 1 1]

-- Cycle fingerprint ca52816dc1c1187402669d6f664f215d6c96901cf41f2092ebc950882e40c225.
def localCycle00312 : Cycle where
  length := 8
  data := {
    node := ![.distance 2 5, .distance 2 4, .distance 1 2, .theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 2 5]
    constant := ![0, -1, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, false, false, false, false, false, false] }
  origin := ![.gapLower 2 3, .triangle 16 0, .gapLower 1 0, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 30 0]

-- Cycle fingerprint cc2c1ebd291b43dbe81c1fc0a42b5def231af5f306622d83738bafeb821d5918.
def localCycle00313 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 4 5, .theta 4, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4]
    constant := ![0, -1, 0, 0, -1, 0, 0, 0, 2, -2]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, true, false, true, true, true, false, false] }
  origin := ![.triangle 19 1, .triangle 21 0, .triangle 32 1, .triangle 34 1, .corridorLower 4 5, .thetaNext 3, .thetaNext 2, .thetaNext 1, .gapLower 1 6, .gapLower 1 5]

-- Cycle fingerprint cc99576c139647ffffeb4aee17b9a6a9cd6f5f57b988c31c0dbd3d6ea14a0fff.
def localCycle00314 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 4]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 23 1]

-- Cycle fingerprint cd6c5d3ac58b6fd4fe593b1cb0beb7ce3d30e8e062b6e2217d1653e5c2f8c9dd.
def localCycle00315 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -3, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint ce19faa6dc5a6132fd57f439170a6199768b2afea48048bc9a52b3c232028e4d.
def localCycle00316 : Cycle where
  length := 3
  data := {
    node := ![.distance 4 6, .distance 1 4, .distance 1 6, .distance 4 6]
    constant := ![2, -3, 0]
    coefficient := ![0, 0, 0]
    strict := ![true, false, true] }
  origin := ![.gapUpper 4 2, .gapLower 1 4, .triangle 23 1]

-- Cycle fingerprint cf6a4c2eac1b1b019f415c208c4d1bb6e2c1cb73e017cf47d8ffe0a97ecf011a.
def localCycle00317 : Cycle where
  length := 6
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 5 6, .distance 4 5, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0, 0]
    strict := ![true, true, false, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 30 1, .triangle 34 0, .triangle 31 0, .triangle 9 0, .triangle 5 1]

-- Cycle fingerprint cfa0539ed448bff5c39132ad53889df9463ca5011fc791dca9d309d1449d90e8.
def localCycle00318 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 3 5, .distance 5 6, .distance 4 6, .distance 1 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, -1, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 31 2, .triangle 33 0, .triangle 34 2, .triangle 23 0, .triangle 22 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint cfe59859940d7804a0c118fcc394d1e7b5cefc571e405e0111e59bc55164fbfc.
def localCycle00319 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![4, 0, -1, 0, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2, .gapLower 1 4, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint d0885a93867537d8d71c15c15c9fc6e8813fbf9dffd1a35ec521fa6726ac73a0.
def localCycle00320 : Cycle where
  length := 11
  data := {
    node := ![.theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5]
    constant := ![3, 0, -1, -1, 0, -1, -2, -2, 0, 0, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, false, false, true, false, false, false, true, false, false] }
  origin := ![.corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0, .thetaNext 0, .thetaLower 0, .thetaUpper 5]

-- Cycle fingerprint d0c02935cee65de9c965c1001c0a9bf527348f1810265316d7a9cea226ca00a5.
def localCycle00321 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 4, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4]
    constant := ![-1, 3, -1, -2, -2]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, false, false, false] }
  origin := ![.corridorLower 1 4, .corridorUpper 0 1, .triangle 3 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint d1237381d93bfb0ea53ba3ac5dc2c60af1aefa7db246a186eaf00ced2debca73.
def localCycle00322 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .triangle 22 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d14eb4a65bca3bb40a170776684ca07e4e56867ddcd54a98f236973a5f060808.
def localCycle00323 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![-1, 0, 0, 2, -2, -2]
    coefficient := ![0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, true, false, false] }
  origin := ![.corridorLower 1 5, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .gapLower 1 3]

-- Cycle fingerprint d2050bbaf7fe21347bc44bfb3e5cc1e05f07b2c48308608f630243e20b0fc2f2.
def localCycle00324 : Cycle where
  length := 8
  data := {
    node := ![.zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 2, 0, 0, -2, 0, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, true, false, true, false, false] }
  origin := ![.thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 22 2, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d25c87b06675fe8a4779678b5de85f08c0919e649ee06ebac4726f87ca6d4761.
def localCycle00325 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, -2, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint d5c563cca8ac08f0574a16611f0d727cac5810fe398bc07046a52ba1a80bc379.
def localCycle00326 : Cycle where
  length := 11
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .theta 0, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6]
    constant := ![0, -1, -2, -1, 0, 0, 0, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0]
    strict := ![true, false, false, false, true, false, false, false, true, false, false] }
  origin := ![.triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .thetaNext 0, .thetaLower 0, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0]

-- Cycle fingerprint d6de72a1d835151b50b854bdef41625f60ec9f2903ccc088c20cd3297d8d59c7.
def localCycle00327 : Cycle where
  length := 7
  data := {
    node := ![.zero, .theta 6, .distance 5 6, .distance 4 5, .distance 2 4, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, -1, -1, -1, -2, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false] }
  origin := ![.thetaUpper 6, .corridorUpper 5 6, .triangle 34 0, .triangle 28 0, .triangle 16 0, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint d83c7a90fa3b1341e81b05bd142467b8cfe71812bbee765e8831bd78f6af4c08.
def localCycle00328 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![3, -1, 0, -3, -1]
    coefficient := ![1, 0, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.corridorUpper 0 1, .triangle 3 0, .triangle 22 1, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint d9d6f6e72c57bf4f39f9b34e116e3b5a5669ef60a89bd9bbbb6ad9954dc8de51.
def localCycle00329 : Cycle where
  length := 8
  data := {
    node := ![.distance 3 5, .theta 3, .theta 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 3 6, .distance 3 5]
    constant := ![-1, 0, 0, 3, -3, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false, true] }
  origin := ![.corridorLower 3 5, .thetaNext 2, .thetaNext 1, .corridorUpper 0 1, .gapLower 1 5, .triangle 19 1, .triangle 21 0, .triangle 33 1]

-- Cycle fingerprint da8104f05aedbe4ed1f580c12cfb91b59a10631a5564952788f87b6a5034a31c.
def localCycle00330 : Cycle where
  length := 6
  data := {
    node := ![.theta 4, .distance 3 4, .distance 0 3, .distance 3 5, .distance 5 6, .distance 4 5, .theta 4]
    constant := ![3, -1, -1, -1, -1, -1]
    coefficient := ![1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false] }
  origin := ![.corridorUpper 3 4, .triangle 9 0, .triangle 10 0, .triangle 33 0, .triangle 34 0, .corridorLower 4 5]

-- Cycle fingerprint dd80f9b58a1466cc24860f87fb3789f13a35ce60b0f7adf7cfd1f5801f182a11.
def localCycle00331 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 6, .distance 3 6, .distance 2 3, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 6, .distance 5 6, .distance 4 6]
    constant := ![0, -1, -1, 0, -1, 0, -3, 0, 0, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 0]
    strict := ![true, false, false, true, false, true, false, false, false, false, true] }
  origin := ![.triangle 32 2, .triangle 27 0, .triangle 26 0, .triangle 31 1, .triangle 19 0, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 6, .corridorUpper 5 6, .triangle 34 2]

-- Cycle fingerprint dfe85cb175d121e3866c51c513f6f6c6532dd7e4be338bd1015af23b328aed15.
def localCycle00332 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, -2, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 19 1, .triangle 21 2, .gapLower 1 2, .triangle 17 1, .corridorLower 1 2]

-- Cycle fingerprint e00a473c2ef422b6e2a32b2100c8005c4b860b1703e1e0041ceb865f3bf7a6ad.
def localCycle00333 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, 0, -1, -1, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 22 0, .triangle 19 1, .corridorLower 1 3]

-- Cycle fingerprint e10f1a0a9681f21d28aa61300bf4ce7f7172e710512d152baf2f5def1c81a1e3.
def localCycle00334 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 6, .distance 0 4, .distance 4 5, .distance 1 5, .distance 1 4, .theta 1]
    constant := ![2, 0, 0, -1, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 2, .triangle 13 1, .triangle 12 0, .triangle 22 2, .gapLower 1 3, .corridorLower 1 4]

-- Cycle fingerprint e1e49daf45d0ddccc22269a3b5e6072afa9945b958097fd226ed860e1aaaeadf.
def localCycle00335 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1]
    constant := ![2, 0, -1, -1, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0]

-- Cycle fingerprint e2b66063a93cbc068573e823cc51ba036775f31582bed56cdbe31049ed87d019.
def localCycle00336 : Cycle where
  length := 8
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![4, 0, -1, -1, -2, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, false, false, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint e35715b71686fe19f595092288147ceaebf1b13236fc350fb1e53d15ec8c6087.
def localCycle00337 : Cycle where
  length := 12
  data := {
    node := ![.distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6]
    constant := ![0, -1, -2, -1, 2, -1, -1, -1, 3, 0, -1, -1]
    coefficient := ![0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
    strict := ![true, false, false, false, false, false, false, false, false, true, false, false] }
  origin := ![.triangle 32 1, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0]

-- Cycle fingerprint e527cd202b539fac28abd9166ac5ff78f2799bc721ab76458e6415ac67b603ed.
def localCycle00338 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, 0, -2]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 0, .triangle 19 1, .triangle 21 2, .triangle 24 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e679a0abce37fb81368e1f4baf7db26b489d6cac305931e3361adc2c68cba573.
def localCycle00339 : Cycle where
  length := 10
  data := {
    node := ![.distance 2 3, .distance 2 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3]
    constant := ![0, -1, -1, 0, -1, 0, -2, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, false, false, true, false, false, false, false] }
  origin := ![.triangle 26 2, .triangle 30 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0, .triangle 15 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3]

-- Cycle fingerprint e7452657dcec7ca0af7f642bf043bedcef8caad11b5ca78ac4c7d740a97516ad.
def localCycle00340 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 6, .distance 1 3]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .gapLower 1 5, .triangle 21 1]

-- Cycle fingerprint e75d5853e41c0d68de96743484369e1f5cf9a998bf7f82cdf1fd8907d2209d81.
def localCycle00341 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, -1, 0, 0, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint e7ca81d31fdb9b7449effe18fe1f9338a09e97947b15e4b9f8e440898af5cb21.
def localCycle00342 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 4, .theta 1, .distance 0 1, .distance 0 5, .distance 5 6, .distance 1 6]
    constant := ![-2, -2, -1, 4, 0, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 4, .gapLower 1 3, .corridorLower 1 4, .gapLower 1 6, .triangle 3 2, .triangle 14 0, .triangle 24 2]

-- Cycle fingerprint e8cc5201c713c410c522036742bdb2c4c38795d2812c4ef429546e1b23e1b40a.
def localCycle00343 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 4, .distance 1 6, .distance 1 5, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-2, 0, 0, 0, 0, -2, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, false, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 23 2, .triangle 24 1, .gapLower 1 2, .triangle 15 1, .gapLower 1 0, .corridorUpper 0 1]

-- Cycle fingerprint e98c04f8a259388313d0b9921c66e363f31c2cf6b6aafd635c83636ddf2e7789.
def localCycle00344 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 6, .distance 1 5, .distance 1 3, .theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 6]
    constant := ![-2, 0, 0, 3, -1, -1, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, true, false, false, false, false, true] }
  origin := ![.gapLower 1 4, .triangle 20 1, .gapLower 3 0, .corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 23 2]

-- Cycle fingerprint ea22979939b76075df732820c9e18837edddef32a9e3fb48d69c7b470b5347cf.
def localCycle00345 : Cycle where
  length := 11
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 4 6, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, -1, -1, 0, 0, -1, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false, true, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 32 0, .triangle 23 0, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .thetaLower 1]

-- Cycle fingerprint eb33b60130245e9d137dcfb28e6715c74f87d97a063e80155b6a9720d12520ad.
def localCycle00346 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, -2, 0, -1, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, false, true, false, false, false] }
  origin := ![.triangle 22 1, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint ebfe432273e518d9e3f293e895c343528a35f354596ee2b8317a3458d3aa930d.
def localCycle00347 : Cycle where
  length := 9
  data := {
    node := ![.distance 5 6, .distance 1 5, .distance 1 4, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6]
    constant := ![-1, -2, 0, -2, 0, 0, 3, -1, -1]
    coefficient := ![0, 0, 0, 0, 0, 1, 1, 0, 0]
    strict := ![false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 24 0, .gapLower 1 3, .triangle 16 1, .gapLower 1 0, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0]

-- Cycle fingerprint ee6c5d9e274808f2938c4fc39720a0ff105e78daf937c7c44c3c5d97f4f4bc51.
def localCycle00348 : Cycle where
  length := 9
  data := {
    node := ![.theta 3, .distance 2 3, .distance 2 4, .distance 2 5, .distance 5 6, .distance 4 6, .distance 0 4, .distance 4 5, .theta 4, .theta 3]
    constant := ![3, 0, 0, -1, 0, -1, -1, -1, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, true, false, true, false, false, false, true] }
  origin := ![.corridorUpper 2 3, .triangle 25 2, .triangle 28 2, .triangle 30 0, .triangle 34 2, .triangle 13 0, .triangle 12 0, .corridorLower 4 5, .thetaNext 3]

-- Cycle fingerprint efccb330ac7ec9b5fa4c5301c828c95a0658fad8890ea00c77a1689bf64bc3e1.
def localCycle00349 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 6, .distance 3 4, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, 0, -1, -1, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 27 0, .triangle 32 1, .triangle 31 0, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Cycle fingerprint f1309f3b5e43f537d3d64dff0430d186baca95743b88a4de1aa087ace16d7431.
def localCycle00350 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 1 6, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 3, -1, 0, -2, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 0, .triangle 24 2, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint f1ce4a7ab40af63ee8397d36dd878fe60ddfdba0acb192168035f724efd675a8.
def localCycle00351 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 2]
    constant := ![-2, 3, -1, 0, -2, 0]
    coefficient := ![0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, true] }
  origin := ![.gapLower 1 0, .corridorUpper 0 1, .triangle 2 0, .triangle 19 1, .gapLower 1 3, .triangle 18 1]

-- Cycle fingerprint f23cd3cf85103c84afe1bfbb62fdf5237fc7af2899d6a83a1f335e93060deb38.
def localCycle00352 : Cycle where
  length := 4
  data := {
    node := ![.distance 1 4, .distance 1 3, .distance 3 6, .distance 4 6, .distance 1 4]
    constant := ![-2, -1, 0, 2]
    coefficient := ![0, 0, 0, 0]
    strict := ![false, false, true, true] }
  origin := ![.gapLower 1 4, .triangle 21 0, .triangle 32 1, .gapUpper 4 2]

-- Cycle fingerprint f252d03633b5a916127c6b60091ad5be9547a744c6d6720030dd5d4ab5934900.
def localCycle00353 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 0 5]
    constant := ![-1, -1, 0, 0, -3, -1, 3, 0]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0]
    strict := ![false, false, false, true, false, false, false, true] }
  origin := ![.triangle 14 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 3 2]

-- Cycle fingerprint f34fd7af36d02f599b969821f2e7288927dc344f25f7b7546d1325ffe1fa70e9.
def localCycle00354 : Cycle where
  length := 8
  data := {
    node := ![.distance 0 1, .distance 0 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![0, -1, -1, 0, -3, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 1]
    strict := ![true, false, false, false, false, true, false, false] }
  origin := ![.triangle 3 2, .triangle 14 0, .triangle 24 0, .gapLower 1 3, .gapLower 1 2, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint f40068904cadff5c258d8da65c3a432502c4880f56ee53bb220c044ba0a14b53.
def localCycle00355 : Cycle where
  length := 5
  data := {
    node := ![.theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .theta 1]
    constant := ![0, 0, 2, -3, -1]
    coefficient := ![0, 1, 0, 0, 0]
    strict := ![false, false, true, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .gapLower 1 4, .corridorLower 1 4]

-- Cycle fingerprint f4b5c04d1b84d241ace2b7c2ef9ce12803b283cf1114766d392d9b7d81430385.
def localCycle00356 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 2, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3, .distance 1 6, .distance 1 5]
    constant := ![-3, -1, 3, -1, 0, 0, 0]
    coefficient := ![0, 0, 1, 0, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .corridorUpper 0 1, .triangle 2 0, .triangle 19 1, .triangle 21 2, .triangle 24 1]

-- Cycle fingerprint f4ebcdb9bdcc44c823204f769b2325adacdf14fd9d6c2d9a5c99641abebcf9fc.
def localCycle00357 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 6, .distance 1 4, .distance 1 5, .theta 1, .distance 0 1, .distance 1 6]
    constant := ![0, -2, -1, 2, -1]
    coefficient := ![0, 0, 0, 1, 0]
    strict := ![true, false, false, false, false] }
  origin := ![.triangle 23 1, .gapLower 1 3, .corridorLower 1 5, .gapLower 1 6, .triangle 4 0]

-- Cycle fingerprint f55dde6233a9bbe4b063e56852ea082281522e9be247f616c047dcbb510d1e3c.
def localCycle00358 : Cycle where
  length := 7
  data := {
    node := ![.distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1]
    constant := ![-3, 0, 0, 0, 0, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1]
    strict := ![false, true, true, true, true, false, false] }
  origin := ![.gapLower 1 5, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2, .corridorUpper 0 1]

-- Cycle fingerprint f6baab0e0b6bce8fccc903afc8f9ba48bf1e068086e38077a6249eace39e34b2.
def localCycle00359 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 0 4, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, 0, 0, 0, -3, -1, 0, 0, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1]
    strict := ![true, false, false, true, false, true, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .gapLower 4 2, .triangle 2 1, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 5, .corridorUpper 4 5]

-- Cycle fingerprint f7197ba773ae20e6bf645aec9aaf86303b10bfc18c7b9bc4efc82ee16f6744a9.
def localCycle00360 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![1, -1, 0, 0, 0, 0, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, true, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .triangle 15 1, .corridorLower 1 2]

-- Cycle fingerprint f771b9b5b0f7d262254ad10f74e986bd49ad5165861322bf2ad3039ab915c80e.
def localCycle00361 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![2, -1, 0, 0, 0, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, true, false, false] }
  origin := ![.gapLower 1 6, .triangle 4 0, .triangle 24 1, .triangle 22 1, .triangle 19 1, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f82d3cb9287cbb13d95d8f5d48c273c7d5c0e9f266740f9fc0b625bced52173d.
def localCycle00362 : Cycle where
  length := 5
  data := {
    node := ![.distance 0 2, .distance 2 6, .distance 4 6, .distance 3 4, .distance 0 3, .distance 0 2]
    constant := ![2, 0, -1, -1, 0]
    coefficient := ![0, 0, 0, 0, 0]
    strict := ![true, true, false, false, true] }
  origin := ![.gapUpper 2 2, .triangle 29 1, .triangle 32 0, .triangle 9 0, .triangle 5 1]

-- Cycle fingerprint f86a7ba0ae360c2fad4d23244eb242538be89ee7ae9d395751c6e84d15a36c0b.
def localCycle00363 : Cycle where
  length := 9
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 5 6, .distance 3 5, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, -1, -1, 0, -1, -2, -1]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 34 0, .triangle 33 0, .gapLower 3 3, .triangle 19 0, .gapLower 1 1, .corridorLower 1 2]

-- Cycle fingerprint f8956432bf5bb39f46ca001fc8d2ac149f57409128b6660f15c7c81325008600.
def localCycle00364 : Cycle where
  length := 5
  data := {
    node := ![.theta 5, .distance 4 5, .distance 2 4, .distance 2 6, .theta 6, .theta 5]
    constant := ![3, -1, 0, -2, 0]
    coefficient := ![1, 0, 0, -1, 0]
    strict := ![false, false, true, true, true] }
  origin := ![.corridorUpper 4 5, .triangle 28 0, .triangle 29 2, .gapUpper 6 6, .thetaNext 5]

-- Cycle fingerprint fa90d47e418d7368c064ce35a27894f8731a605fb8e601cc2e1a9629e6d241e9.
def localCycle00365 : Cycle where
  length := 7
  data := {
    node := ![.theta 3, .distance 2 3, .distance 3 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 3]
    constant := ![3, -1, -1, 0, -1, -2, 0]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, false] }
  origin := ![.corridorUpper 2 3, .triangle 25 0, .triangle 32 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .gapLower 3 0]

-- Cycle fingerprint fb3d8a883566edb5dca2a4b65d0a8fdde5a663bf51a75230de3c3c1060dac68c.
def localCycle00366 : Cycle where
  length := 10
  data := {
    node := ![.theta 1, .zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1]
    constant := ![0, 0, 3, 0, -1, -1, 0, -1, -2, -2]
    coefficient := ![0, 1, 1, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, false, true, false, false, true, false, false, false] }
  origin := ![.thetaLower 1, .thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .gapLower 1 1, .gapLower 1 0]

-- Cycle fingerprint fb73ba3bae1068e518226b7e2d400e3dd9c9921f284ead3db387f0206e36e9f6.
def localCycle00367 : Cycle where
  length := 10
  data := {
    node := ![.distance 1 3, .distance 1 2, .theta 1, .zero, .theta 3, .distance 2 3, .distance 3 5, .distance 5 6, .distance 1 5, .distance 1 4, .distance 1 3]
    constant := ![-2, -1, 0, 0, 3, -1, -1, -1, -2, 0]
    coefficient := ![0, 0, 0, 1, 1, 0, 0, 0, 0, 0]
    strict := ![false, false, false, false, false, false, false, false, false, true] }
  origin := ![.gapLower 1 1, .corridorLower 1 2, .thetaLower 1, .thetaUpper 3, .corridorUpper 2 3, .triangle 26 0, .triangle 33 0, .triangle 24 0, .gapLower 1 3, .triangle 19 1]

-- Cycle fingerprint fc41c68ea41354aa0e74dadc0aae029f4fd0607f16f0fc3843d6ac2effd94c9f.
def localCycle00368 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 4, .distance 1 5]
    constant := ![-3, -1, 0, 0, 2, 0, 0]
    coefficient := ![0, 0, 0, 1, 0, 0, 0]
    strict := ![false, false, false, false, true, true, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 23 1, .triangle 22 2]

-- Cycle fingerprint fc433a5e3ae79154cbbf5ce8cd836bdbd15ce9eaa1e5b40c9c2d8ec30503658a.
def localCycle00369 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5]
    constant := ![0, 0, 0, -2, 2, -1]
    coefficient := ![0, 0, 0, 0, 1, 0]
    strict := ![true, true, true, false, false, false] }
  origin := ![.triangle 22 1, .triangle 19 1, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0]

-- Cycle fingerprint fcb03297969ed00a9c1b821dcebd7e8a239558c2a6d907eb9b701f811f7bcc57.
def localCycle00370 : Cycle where
  length := 7
  data := {
    node := ![.distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .zero, .theta 6, .distance 1 6, .distance 1 5]
    constant := ![-2, -2, -1, 0, 0, 2, 0]
    coefficient := ![0, 0, 0, 0, 1, 0, 0]
    strict := ![false, false, false, false, false, true, true] }
  origin := ![.gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaLower 1, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1]

-- Cycle fingerprint fd3ba523112913f3a2c25a755f61b80b1e557224fc91d84f7ee00a3dec6ce484.
def localCycle00371 : Cycle where
  length := 4
  data := {
    node := ![.distance 0 1, .distance 1 5, .distance 1 6, .theta 1, .distance 0 1]
    constant := ![-2, -2, -1, 3]
    coefficient := ![0, 0, 0, 1]
    strict := ![false, false, false, false] }
  origin := ![.gapLower 1 5, .gapLower 1 4, .corridorLower 1 6, .corridorUpper 0 1]

-- Cycle fingerprint fd7a389ddb99755d9d7c4e7ebb9d02c28f5b96f5c865ee8e1c39cbcb0e4831e0.
def localCycle00372 : Cycle where
  length := 10
  data := {
    node := ![.zero, .theta 5, .distance 4 5, .distance 3 5, .distance 2 3, .distance 3 6, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .zero]
    constant := ![0, 3, 0, -1, -1, 0, -1, 0, -3, 0]
    coefficient := ![1, 1, 0, 0, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, false, false, true, false, true, false, false] }
  origin := ![.thetaUpper 5, .corridorUpper 4 5, .triangle 31 2, .triangle 26 0, .triangle 27 0, .triangle 32 1, .triangle 19 0, .triangle 15 1, .gapLower 1 0, .thetaLower 1]

-- Cycle fingerprint fe0d7fec3a87b5cfdb1af6ea8f832cfe8da51bec70a2786e7f47c817480b732b.
def localCycle00373 : Cycle where
  length := 8
  data := {
    node := ![.theta 0, .zero, .theta 6, .distance 1 6, .distance 1 5, .distance 1 4, .distance 1 3, .theta 1, .theta 0]
    constant := ![0, 0, 2, 0, -2, -2, -1, 0]
    coefficient := ![0, 1, 0, 0, 0, 0, 0, 0]
    strict := ![false, false, true, true, false, false, false, true] }
  origin := ![.thetaLower 0, .thetaUpper 6, .gapUpper 6 0, .triangle 24 1, .gapLower 1 3, .gapLower 1 2, .corridorLower 1 3, .thetaNext 0]

-- Cycle fingerprint fe168f48d48af381052638b248b8be63bcf7b607be1b265a7edafc808bfd6f1b.
def localCycle00374 : Cycle where
  length := 5
  data := {
    node := ![.distance 1 5, .distance 1 3, .theta 1, .distance 0 1, .distance 1 6, .distance 1 5]
    constant := ![-2, -1, 3, -2, 0]
    coefficient := ![0, 0, 1, 0, 0]
    strict := ![false, false, false, false, true] }
  origin := ![.gapLower 1 2, .corridorLower 1 3, .corridorUpper 0 1, .gapLower 1 5, .triangle 24 1]

-- Cycle fingerprint feea04c486af2863b58b98ba7ffdf34a005a97b470d586b355d3c8331e84e320.
def localCycle00375 : Cycle where
  length := 7
  data := {
    node := ![.theta 1, .distance 0 1, .distance 0 4, .distance 4 6, .distance 4 5, .distance 1 4, .distance 1 3, .theta 1]
    constant := ![2, 0, -1, 0, -1, -2, -1]
    coefficient := ![1, 0, 0, 0, 0, 0, 0]
    strict := ![false, true, false, true, false, false, false] }
  origin := ![.gapLower 1 6, .triangle 2 2, .triangle 13 0, .triangle 34 1, .triangle 22 0, .gapLower 1 2, .corridorLower 1 3]

-- Cycle fingerprint ff70f0b2a7db439003d4c9e84982117957739dd4b03b05757629e20b011ba8dd.
def localCycle00376 : Cycle where
  length := 11
  data := {
    node := ![.distance 4 5, .distance 3 5, .distance 2 3, .distance 3 4, .distance 1 3, .distance 1 2, .theta 1, .distance 0 1, .distance 1 5, .distance 5 6, .theta 5, .distance 4 5]
    constant := ![0, -1, -1, -1, 0, -2, 2, -1, -1, -1, 3]
    coefficient := ![0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1]
    strict := ![true, false, false, false, true, false, false, false, false, false, false] }
  origin := ![.triangle 31 2, .triangle 26 0, .triangle 25 0, .triangle 19 0, .triangle 15 1, .gapLower 1 0, .gapLower 1 6, .triangle 3 0, .triangle 24 0, .corridorLower 5 6, .corridorUpper 4 5]

-- Cycle fingerprint ff766b22677ce12c9d51006b9f4adc233d121543198befe0821ab913277772a0.
def localCycle00377 : Cycle where
  length := 6
  data := {
    node := ![.distance 1 3, .distance 1 6, .distance 1 5, .theta 1, .distance 0 1, .distance 1 4, .distance 1 3]
    constant := ![0, -2, -1, 3, -2, 0]
    coefficient := ![0, 0, 0, 1, 0, 0]
    strict := ![true, false, false, false, false, true] }
  origin := ![.triangle 21 2, .gapLower 1 2, .corridorLower 1 5, .corridorUpper 0 1, .gapLower 1 5, .triangle 19 1]

def library : Library := fun id => if id < 189 then (if id < 94 then (if id < 47 then (if id < 23 then (if id < 11 then (if id < 5 then (if id < 2 then (if id < 1 then (if id = 0 then some localCycle00000 else none) else (if id = 1 then some localCycle00001 else none)) else (if id < 3 then (if id = 2 then some localCycle00002 else none) else (if id < 4 then (if id = 3 then some localCycle00003 else none) else (if id = 4 then some localCycle00004 else none)))) else (if id < 8 then (if id < 6 then (if id = 5 then some localCycle00005 else none) else (if id < 7 then (if id = 6 then some localCycle00006 else none) else (if id = 7 then some localCycle00007 else none))) else (if id < 9 then (if id = 8 then some localCycle00008 else none) else (if id < 10 then (if id = 9 then some localCycle00009 else none) else (if id = 10 then some localCycle00010 else none))))) else (if id < 17 then (if id < 14 then (if id < 12 then (if id = 11 then some localCycle00011 else none) else (if id < 13 then (if id = 12 then some localCycle00012 else none) else (if id = 13 then some localCycle00013 else none))) else (if id < 15 then (if id = 14 then some localCycle00014 else none) else (if id < 16 then (if id = 15 then some localCycle00015 else none) else (if id = 16 then some localCycle00016 else none)))) else (if id < 20 then (if id < 18 then (if id = 17 then some localCycle00017 else none) else (if id < 19 then (if id = 18 then some localCycle00018 else none) else (if id = 19 then some localCycle00019 else none))) else (if id < 21 then (if id = 20 then some localCycle00020 else none) else (if id < 22 then (if id = 21 then some localCycle00021 else none) else (if id = 22 then some localCycle00022 else none)))))) else (if id < 35 then (if id < 29 then (if id < 26 then (if id < 24 then (if id = 23 then some localCycle00023 else none) else (if id < 25 then (if id = 24 then some localCycle00024 else none) else (if id = 25 then some localCycle00025 else none))) else (if id < 27 then (if id = 26 then some localCycle00026 else none) else (if id < 28 then (if id = 27 then some localCycle00027 else none) else (if id = 28 then some localCycle00028 else none)))) else (if id < 32 then (if id < 30 then (if id = 29 then some localCycle00029 else none) else (if id < 31 then (if id = 30 then some localCycle00030 else none) else (if id = 31 then some localCycle00031 else none))) else (if id < 33 then (if id = 32 then some localCycle00032 else none) else (if id < 34 then (if id = 33 then some localCycle00033 else none) else (if id = 34 then some localCycle00034 else none))))) else (if id < 41 then (if id < 38 then (if id < 36 then (if id = 35 then some localCycle00035 else none) else (if id < 37 then (if id = 36 then some localCycle00036 else none) else (if id = 37 then some localCycle00037 else none))) else (if id < 39 then (if id = 38 then some localCycle00038 else none) else (if id < 40 then (if id = 39 then some localCycle00039 else none) else (if id = 40 then some localCycle00040 else none)))) else (if id < 44 then (if id < 42 then (if id = 41 then some localCycle00041 else none) else (if id < 43 then (if id = 42 then some localCycle00042 else none) else (if id = 43 then some localCycle00043 else none))) else (if id < 45 then (if id = 44 then some localCycle00044 else none) else (if id < 46 then (if id = 45 then some localCycle00045 else none) else (if id = 46 then some localCycle00046 else none))))))) else (if id < 70 then (if id < 58 then (if id < 52 then (if id < 49 then (if id < 48 then (if id = 47 then some localCycle00047 else none) else (if id = 48 then some localCycle00048 else none)) else (if id < 50 then (if id = 49 then some localCycle00049 else none) else (if id < 51 then (if id = 50 then some localCycle00050 else none) else (if id = 51 then some localCycle00051 else none)))) else (if id < 55 then (if id < 53 then (if id = 52 then some localCycle00052 else none) else (if id < 54 then (if id = 53 then some localCycle00053 else none) else (if id = 54 then some localCycle00054 else none))) else (if id < 56 then (if id = 55 then some localCycle00055 else none) else (if id < 57 then (if id = 56 then some localCycle00056 else none) else (if id = 57 then some localCycle00057 else none))))) else (if id < 64 then (if id < 61 then (if id < 59 then (if id = 58 then some localCycle00058 else none) else (if id < 60 then (if id = 59 then some localCycle00059 else none) else (if id = 60 then some localCycle00060 else none))) else (if id < 62 then (if id = 61 then some localCycle00061 else none) else (if id < 63 then (if id = 62 then some localCycle00062 else none) else (if id = 63 then some localCycle00063 else none)))) else (if id < 67 then (if id < 65 then (if id = 64 then some localCycle00064 else none) else (if id < 66 then (if id = 65 then some localCycle00065 else none) else (if id = 66 then some localCycle00066 else none))) else (if id < 68 then (if id = 67 then some localCycle00067 else none) else (if id < 69 then (if id = 68 then some localCycle00068 else none) else (if id = 69 then some localCycle00069 else none)))))) else (if id < 82 then (if id < 76 then (if id < 73 then (if id < 71 then (if id = 70 then some localCycle00070 else none) else (if id < 72 then (if id = 71 then some localCycle00071 else none) else (if id = 72 then some localCycle00072 else none))) else (if id < 74 then (if id = 73 then some localCycle00073 else none) else (if id < 75 then (if id = 74 then some localCycle00074 else none) else (if id = 75 then some localCycle00075 else none)))) else (if id < 79 then (if id < 77 then (if id = 76 then some localCycle00076 else none) else (if id < 78 then (if id = 77 then some localCycle00077 else none) else (if id = 78 then some localCycle00078 else none))) else (if id < 80 then (if id = 79 then some localCycle00079 else none) else (if id < 81 then (if id = 80 then some localCycle00080 else none) else (if id = 81 then some localCycle00081 else none))))) else (if id < 88 then (if id < 85 then (if id < 83 then (if id = 82 then some localCycle00082 else none) else (if id < 84 then (if id = 83 then some localCycle00083 else none) else (if id = 84 then some localCycle00084 else none))) else (if id < 86 then (if id = 85 then some localCycle00085 else none) else (if id < 87 then (if id = 86 then some localCycle00086 else none) else (if id = 87 then some localCycle00087 else none)))) else (if id < 91 then (if id < 89 then (if id = 88 then some localCycle00088 else none) else (if id < 90 then (if id = 89 then some localCycle00089 else none) else (if id = 90 then some localCycle00090 else none))) else (if id < 92 then (if id = 91 then some localCycle00091 else none) else (if id < 93 then (if id = 92 then some localCycle00092 else none) else (if id = 93 then some localCycle00093 else none)))))))) else (if id < 141 then (if id < 117 then (if id < 105 then (if id < 99 then (if id < 96 then (if id < 95 then (if id = 94 then some localCycle00094 else none) else (if id = 95 then some localCycle00095 else none)) else (if id < 97 then (if id = 96 then some localCycle00096 else none) else (if id < 98 then (if id = 97 then some localCycle00097 else none) else (if id = 98 then some localCycle00098 else none)))) else (if id < 102 then (if id < 100 then (if id = 99 then some localCycle00099 else none) else (if id < 101 then (if id = 100 then some localCycle00100 else none) else (if id = 101 then some localCycle00101 else none))) else (if id < 103 then (if id = 102 then some localCycle00102 else none) else (if id < 104 then (if id = 103 then some localCycle00103 else none) else (if id = 104 then some localCycle00104 else none))))) else (if id < 111 then (if id < 108 then (if id < 106 then (if id = 105 then some localCycle00105 else none) else (if id < 107 then (if id = 106 then some localCycle00106 else none) else (if id = 107 then some localCycle00107 else none))) else (if id < 109 then (if id = 108 then some localCycle00108 else none) else (if id < 110 then (if id = 109 then some localCycle00109 else none) else (if id = 110 then some localCycle00110 else none)))) else (if id < 114 then (if id < 112 then (if id = 111 then some localCycle00111 else none) else (if id < 113 then (if id = 112 then some localCycle00112 else none) else (if id = 113 then some localCycle00113 else none))) else (if id < 115 then (if id = 114 then some localCycle00114 else none) else (if id < 116 then (if id = 115 then some localCycle00115 else none) else (if id = 116 then some localCycle00116 else none)))))) else (if id < 129 then (if id < 123 then (if id < 120 then (if id < 118 then (if id = 117 then some localCycle00117 else none) else (if id < 119 then (if id = 118 then some localCycle00118 else none) else (if id = 119 then some localCycle00119 else none))) else (if id < 121 then (if id = 120 then some localCycle00120 else none) else (if id < 122 then (if id = 121 then some localCycle00121 else none) else (if id = 122 then some localCycle00122 else none)))) else (if id < 126 then (if id < 124 then (if id = 123 then some localCycle00123 else none) else (if id < 125 then (if id = 124 then some localCycle00124 else none) else (if id = 125 then some localCycle00125 else none))) else (if id < 127 then (if id = 126 then some localCycle00126 else none) else (if id < 128 then (if id = 127 then some localCycle00127 else none) else (if id = 128 then some localCycle00128 else none))))) else (if id < 135 then (if id < 132 then (if id < 130 then (if id = 129 then some localCycle00129 else none) else (if id < 131 then (if id = 130 then some localCycle00130 else none) else (if id = 131 then some localCycle00131 else none))) else (if id < 133 then (if id = 132 then some localCycle00132 else none) else (if id < 134 then (if id = 133 then some localCycle00133 else none) else (if id = 134 then some localCycle00134 else none)))) else (if id < 138 then (if id < 136 then (if id = 135 then some localCycle00135 else none) else (if id < 137 then (if id = 136 then some localCycle00136 else none) else (if id = 137 then some localCycle00137 else none))) else (if id < 139 then (if id = 138 then some localCycle00138 else none) else (if id < 140 then (if id = 139 then some localCycle00139 else none) else (if id = 140 then some localCycle00140 else none))))))) else (if id < 165 then (if id < 153 then (if id < 147 then (if id < 144 then (if id < 142 then (if id = 141 then some localCycle00141 else none) else (if id < 143 then (if id = 142 then some localCycle00142 else none) else (if id = 143 then some localCycle00143 else none))) else (if id < 145 then (if id = 144 then some localCycle00144 else none) else (if id < 146 then (if id = 145 then some localCycle00145 else none) else (if id = 146 then some localCycle00146 else none)))) else (if id < 150 then (if id < 148 then (if id = 147 then some localCycle00147 else none) else (if id < 149 then (if id = 148 then some localCycle00148 else none) else (if id = 149 then some localCycle00149 else none))) else (if id < 151 then (if id = 150 then some localCycle00150 else none) else (if id < 152 then (if id = 151 then some localCycle00151 else none) else (if id = 152 then some localCycle00152 else none))))) else (if id < 159 then (if id < 156 then (if id < 154 then (if id = 153 then some localCycle00153 else none) else (if id < 155 then (if id = 154 then some localCycle00154 else none) else (if id = 155 then some localCycle00155 else none))) else (if id < 157 then (if id = 156 then some localCycle00156 else none) else (if id < 158 then (if id = 157 then some localCycle00157 else none) else (if id = 158 then some localCycle00158 else none)))) else (if id < 162 then (if id < 160 then (if id = 159 then some localCycle00159 else none) else (if id < 161 then (if id = 160 then some localCycle00160 else none) else (if id = 161 then some localCycle00161 else none))) else (if id < 163 then (if id = 162 then some localCycle00162 else none) else (if id < 164 then (if id = 163 then some localCycle00163 else none) else (if id = 164 then some localCycle00164 else none)))))) else (if id < 177 then (if id < 171 then (if id < 168 then (if id < 166 then (if id = 165 then some localCycle00165 else none) else (if id < 167 then (if id = 166 then some localCycle00166 else none) else (if id = 167 then some localCycle00167 else none))) else (if id < 169 then (if id = 168 then some localCycle00168 else none) else (if id < 170 then (if id = 169 then some localCycle00169 else none) else (if id = 170 then some localCycle00170 else none)))) else (if id < 174 then (if id < 172 then (if id = 171 then some localCycle00171 else none) else (if id < 173 then (if id = 172 then some localCycle00172 else none) else (if id = 173 then some localCycle00173 else none))) else (if id < 175 then (if id = 174 then some localCycle00174 else none) else (if id < 176 then (if id = 175 then some localCycle00175 else none) else (if id = 176 then some localCycle00176 else none))))) else (if id < 183 then (if id < 180 then (if id < 178 then (if id = 177 then some localCycle00177 else none) else (if id < 179 then (if id = 178 then some localCycle00178 else none) else (if id = 179 then some localCycle00179 else none))) else (if id < 181 then (if id = 180 then some localCycle00180 else none) else (if id < 182 then (if id = 181 then some localCycle00181 else none) else (if id = 182 then some localCycle00182 else none)))) else (if id < 186 then (if id < 184 then (if id = 183 then some localCycle00183 else none) else (if id < 185 then (if id = 184 then some localCycle00184 else none) else (if id = 185 then some localCycle00185 else none))) else (if id < 187 then (if id = 186 then some localCycle00186 else none) else (if id < 188 then (if id = 187 then some localCycle00187 else none) else (if id = 188 then some localCycle00188 else none))))))))) else (if id < 283 then (if id < 236 then (if id < 212 then (if id < 200 then (if id < 194 then (if id < 191 then (if id < 190 then (if id = 189 then some localCycle00189 else none) else (if id = 190 then some localCycle00190 else none)) else (if id < 192 then (if id = 191 then some localCycle00191 else none) else (if id < 193 then (if id = 192 then some localCycle00192 else none) else (if id = 193 then some localCycle00193 else none)))) else (if id < 197 then (if id < 195 then (if id = 194 then some localCycle00194 else none) else (if id < 196 then (if id = 195 then some localCycle00195 else none) else (if id = 196 then some localCycle00196 else none))) else (if id < 198 then (if id = 197 then some localCycle00197 else none) else (if id < 199 then (if id = 198 then some localCycle00198 else none) else (if id = 199 then some localCycle00199 else none))))) else (if id < 206 then (if id < 203 then (if id < 201 then (if id = 200 then some localCycle00200 else none) else (if id < 202 then (if id = 201 then some localCycle00201 else none) else (if id = 202 then some localCycle00202 else none))) else (if id < 204 then (if id = 203 then some localCycle00203 else none) else (if id < 205 then (if id = 204 then some localCycle00204 else none) else (if id = 205 then some localCycle00205 else none)))) else (if id < 209 then (if id < 207 then (if id = 206 then some localCycle00206 else none) else (if id < 208 then (if id = 207 then some localCycle00207 else none) else (if id = 208 then some localCycle00208 else none))) else (if id < 210 then (if id = 209 then some localCycle00209 else none) else (if id < 211 then (if id = 210 then some localCycle00210 else none) else (if id = 211 then some localCycle00211 else none)))))) else (if id < 224 then (if id < 218 then (if id < 215 then (if id < 213 then (if id = 212 then some localCycle00212 else none) else (if id < 214 then (if id = 213 then some localCycle00213 else none) else (if id = 214 then some localCycle00214 else none))) else (if id < 216 then (if id = 215 then some localCycle00215 else none) else (if id < 217 then (if id = 216 then some localCycle00216 else none) else (if id = 217 then some localCycle00217 else none)))) else (if id < 221 then (if id < 219 then (if id = 218 then some localCycle00218 else none) else (if id < 220 then (if id = 219 then some localCycle00219 else none) else (if id = 220 then some localCycle00220 else none))) else (if id < 222 then (if id = 221 then some localCycle00221 else none) else (if id < 223 then (if id = 222 then some localCycle00222 else none) else (if id = 223 then some localCycle00223 else none))))) else (if id < 230 then (if id < 227 then (if id < 225 then (if id = 224 then some localCycle00224 else none) else (if id < 226 then (if id = 225 then some localCycle00225 else none) else (if id = 226 then some localCycle00226 else none))) else (if id < 228 then (if id = 227 then some localCycle00227 else none) else (if id < 229 then (if id = 228 then some localCycle00228 else none) else (if id = 229 then some localCycle00229 else none)))) else (if id < 233 then (if id < 231 then (if id = 230 then some localCycle00230 else none) else (if id < 232 then (if id = 231 then some localCycle00231 else none) else (if id = 232 then some localCycle00232 else none))) else (if id < 234 then (if id = 233 then some localCycle00233 else none) else (if id < 235 then (if id = 234 then some localCycle00234 else none) else (if id = 235 then some localCycle00235 else none))))))) else (if id < 259 then (if id < 247 then (if id < 241 then (if id < 238 then (if id < 237 then (if id = 236 then some localCycle00236 else none) else (if id = 237 then some localCycle00237 else none)) else (if id < 239 then (if id = 238 then some localCycle00238 else none) else (if id < 240 then (if id = 239 then some localCycle00239 else none) else (if id = 240 then some localCycle00240 else none)))) else (if id < 244 then (if id < 242 then (if id = 241 then some localCycle00241 else none) else (if id < 243 then (if id = 242 then some localCycle00242 else none) else (if id = 243 then some localCycle00243 else none))) else (if id < 245 then (if id = 244 then some localCycle00244 else none) else (if id < 246 then (if id = 245 then some localCycle00245 else none) else (if id = 246 then some localCycle00246 else none))))) else (if id < 253 then (if id < 250 then (if id < 248 then (if id = 247 then some localCycle00247 else none) else (if id < 249 then (if id = 248 then some localCycle00248 else none) else (if id = 249 then some localCycle00249 else none))) else (if id < 251 then (if id = 250 then some localCycle00250 else none) else (if id < 252 then (if id = 251 then some localCycle00251 else none) else (if id = 252 then some localCycle00252 else none)))) else (if id < 256 then (if id < 254 then (if id = 253 then some localCycle00253 else none) else (if id < 255 then (if id = 254 then some localCycle00254 else none) else (if id = 255 then some localCycle00255 else none))) else (if id < 257 then (if id = 256 then some localCycle00256 else none) else (if id < 258 then (if id = 257 then some localCycle00257 else none) else (if id = 258 then some localCycle00258 else none)))))) else (if id < 271 then (if id < 265 then (if id < 262 then (if id < 260 then (if id = 259 then some localCycle00259 else none) else (if id < 261 then (if id = 260 then some localCycle00260 else none) else (if id = 261 then some localCycle00261 else none))) else (if id < 263 then (if id = 262 then some localCycle00262 else none) else (if id < 264 then (if id = 263 then some localCycle00263 else none) else (if id = 264 then some localCycle00264 else none)))) else (if id < 268 then (if id < 266 then (if id = 265 then some localCycle00265 else none) else (if id < 267 then (if id = 266 then some localCycle00266 else none) else (if id = 267 then some localCycle00267 else none))) else (if id < 269 then (if id = 268 then some localCycle00268 else none) else (if id < 270 then (if id = 269 then some localCycle00269 else none) else (if id = 270 then some localCycle00270 else none))))) else (if id < 277 then (if id < 274 then (if id < 272 then (if id = 271 then some localCycle00271 else none) else (if id < 273 then (if id = 272 then some localCycle00272 else none) else (if id = 273 then some localCycle00273 else none))) else (if id < 275 then (if id = 274 then some localCycle00274 else none) else (if id < 276 then (if id = 275 then some localCycle00275 else none) else (if id = 276 then some localCycle00276 else none)))) else (if id < 280 then (if id < 278 then (if id = 277 then some localCycle00277 else none) else (if id < 279 then (if id = 278 then some localCycle00278 else none) else (if id = 279 then some localCycle00279 else none))) else (if id < 281 then (if id = 280 then some localCycle00280 else none) else (if id < 282 then (if id = 281 then some localCycle00281 else none) else (if id = 282 then some localCycle00282 else none)))))))) else (if id < 330 then (if id < 306 then (if id < 294 then (if id < 288 then (if id < 285 then (if id < 284 then (if id = 283 then some localCycle00283 else none) else (if id = 284 then some localCycle00284 else none)) else (if id < 286 then (if id = 285 then some localCycle00285 else none) else (if id < 287 then (if id = 286 then some localCycle00286 else none) else (if id = 287 then some localCycle00287 else none)))) else (if id < 291 then (if id < 289 then (if id = 288 then some localCycle00288 else none) else (if id < 290 then (if id = 289 then some localCycle00289 else none) else (if id = 290 then some localCycle00290 else none))) else (if id < 292 then (if id = 291 then some localCycle00291 else none) else (if id < 293 then (if id = 292 then some localCycle00292 else none) else (if id = 293 then some localCycle00293 else none))))) else (if id < 300 then (if id < 297 then (if id < 295 then (if id = 294 then some localCycle00294 else none) else (if id < 296 then (if id = 295 then some localCycle00295 else none) else (if id = 296 then some localCycle00296 else none))) else (if id < 298 then (if id = 297 then some localCycle00297 else none) else (if id < 299 then (if id = 298 then some localCycle00298 else none) else (if id = 299 then some localCycle00299 else none)))) else (if id < 303 then (if id < 301 then (if id = 300 then some localCycle00300 else none) else (if id < 302 then (if id = 301 then some localCycle00301 else none) else (if id = 302 then some localCycle00302 else none))) else (if id < 304 then (if id = 303 then some localCycle00303 else none) else (if id < 305 then (if id = 304 then some localCycle00304 else none) else (if id = 305 then some localCycle00305 else none)))))) else (if id < 318 then (if id < 312 then (if id < 309 then (if id < 307 then (if id = 306 then some localCycle00306 else none) else (if id < 308 then (if id = 307 then some localCycle00307 else none) else (if id = 308 then some localCycle00308 else none))) else (if id < 310 then (if id = 309 then some localCycle00309 else none) else (if id < 311 then (if id = 310 then some localCycle00310 else none) else (if id = 311 then some localCycle00311 else none)))) else (if id < 315 then (if id < 313 then (if id = 312 then some localCycle00312 else none) else (if id < 314 then (if id = 313 then some localCycle00313 else none) else (if id = 314 then some localCycle00314 else none))) else (if id < 316 then (if id = 315 then some localCycle00315 else none) else (if id < 317 then (if id = 316 then some localCycle00316 else none) else (if id = 317 then some localCycle00317 else none))))) else (if id < 324 then (if id < 321 then (if id < 319 then (if id = 318 then some localCycle00318 else none) else (if id < 320 then (if id = 319 then some localCycle00319 else none) else (if id = 320 then some localCycle00320 else none))) else (if id < 322 then (if id = 321 then some localCycle00321 else none) else (if id < 323 then (if id = 322 then some localCycle00322 else none) else (if id = 323 then some localCycle00323 else none)))) else (if id < 327 then (if id < 325 then (if id = 324 then some localCycle00324 else none) else (if id < 326 then (if id = 325 then some localCycle00325 else none) else (if id = 326 then some localCycle00326 else none))) else (if id < 328 then (if id = 327 then some localCycle00327 else none) else (if id < 329 then (if id = 328 then some localCycle00328 else none) else (if id = 329 then some localCycle00329 else none))))))) else (if id < 354 then (if id < 342 then (if id < 336 then (if id < 333 then (if id < 331 then (if id = 330 then some localCycle00330 else none) else (if id < 332 then (if id = 331 then some localCycle00331 else none) else (if id = 332 then some localCycle00332 else none))) else (if id < 334 then (if id = 333 then some localCycle00333 else none) else (if id < 335 then (if id = 334 then some localCycle00334 else none) else (if id = 335 then some localCycle00335 else none)))) else (if id < 339 then (if id < 337 then (if id = 336 then some localCycle00336 else none) else (if id < 338 then (if id = 337 then some localCycle00337 else none) else (if id = 338 then some localCycle00338 else none))) else (if id < 340 then (if id = 339 then some localCycle00339 else none) else (if id < 341 then (if id = 340 then some localCycle00340 else none) else (if id = 341 then some localCycle00341 else none))))) else (if id < 348 then (if id < 345 then (if id < 343 then (if id = 342 then some localCycle00342 else none) else (if id < 344 then (if id = 343 then some localCycle00343 else none) else (if id = 344 then some localCycle00344 else none))) else (if id < 346 then (if id = 345 then some localCycle00345 else none) else (if id < 347 then (if id = 346 then some localCycle00346 else none) else (if id = 347 then some localCycle00347 else none)))) else (if id < 351 then (if id < 349 then (if id = 348 then some localCycle00348 else none) else (if id < 350 then (if id = 349 then some localCycle00349 else none) else (if id = 350 then some localCycle00350 else none))) else (if id < 352 then (if id = 351 then some localCycle00351 else none) else (if id < 353 then (if id = 352 then some localCycle00352 else none) else (if id = 353 then some localCycle00353 else none)))))) else (if id < 366 then (if id < 360 then (if id < 357 then (if id < 355 then (if id = 354 then some localCycle00354 else none) else (if id < 356 then (if id = 355 then some localCycle00355 else none) else (if id = 356 then some localCycle00356 else none))) else (if id < 358 then (if id = 357 then some localCycle00357 else none) else (if id < 359 then (if id = 358 then some localCycle00358 else none) else (if id = 359 then some localCycle00359 else none)))) else (if id < 363 then (if id < 361 then (if id = 360 then some localCycle00360 else none) else (if id < 362 then (if id = 361 then some localCycle00361 else none) else (if id = 362 then some localCycle00362 else none))) else (if id < 364 then (if id = 363 then some localCycle00363 else none) else (if id < 365 then (if id = 364 then some localCycle00364 else none) else (if id = 365 then some localCycle00365 else none))))) else (if id < 372 then (if id < 369 then (if id < 367 then (if id = 366 then some localCycle00366 else none) else (if id < 368 then (if id = 367 then some localCycle00367 else none) else (if id = 368 then some localCycle00368 else none))) else (if id < 370 then (if id = 369 then some localCycle00369 else none) else (if id < 371 then (if id = 370 then some localCycle00370 else none) else (if id = 371 then some localCycle00371 else none)))) else (if id < 375 then (if id < 373 then (if id = 372 then some localCycle00372 else none) else (if id < 374 then (if id = 373 then some localCycle00373 else none) else (if id = 374 then some localCycle00374 else none))) else (if id < 376 then (if id = 375 then some localCycle00375 else none) else (if id < 377 then (if id = 376 then some localCycle00376 else none) else (if id = 377 then some localCycle00377 else none)))))))))

def namedLeaf000 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 0, 6, 2], ![4, 1, 3, 0, 5, 2]], proof := .tail 54 }

theorem namedLeaf000_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18048)) namedLeaf000 = true :=
  by decide +kernel

def namedLeaf001 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 5, 3, 6, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 1, 6, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 6, 0, 2], ![4, 1, 3, 5, 0, 2]], proof := .tail 193 }

theorem namedLeaf001_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18049)) namedLeaf001 = true :=
  by decide +kernel

def namedLeaf002 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 5, 6, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 0, 2, 6], ![4, 3, 1, 0, 2, 5]], proof := .low (![304, 356, 123, 299, 68, 329, 115, 187, 85, 351, 352, 262, 338, 226, 93, 352, 61, 129, 93, 352, 377, 332, 352, 32, 145, 352, 352, 313]) }

theorem namedLeaf002_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18050)) namedLeaf002 = true :=
  by decide +kernel

def namedLeaf003 : LeafData := { rows := ![![2, 5, 6, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 0, 6, 2], ![4, 3, 1, 0, 5, 2]], proof := .tail 51 }

theorem namedLeaf003_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18051)) namedLeaf003 = true :=
  by decide +kernel

def namedLeaf004 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 5, 6, 3, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 1, 6, 0, 2], ![4, 3, 1, 5, 0, 2]], proof := .tail 78 }

theorem namedLeaf004_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18052)) namedLeaf004 = true :=
  by decide +kernel

def namedLeaf005 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 3, 4], ![5, 6, 1, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 3, 6, 1, 0, 2], ![4, 3, 5, 1, 0, 2]], proof := .tail 78 }

theorem namedLeaf005_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18053)) namedLeaf005 = true :=
  by decide +kernel

def namedLeaf006 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 3, 4], ![6, 5, 1, 0, 2, 4], ![5, 6, 1, 0, 2, 3], ![4, 6, 3, 1, 0, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 330 }

theorem namedLeaf006_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18054)) namedLeaf006 = true :=
  by decide +kernel

def namedLeaf007 : LeafData := { rows := ![![2, 6, 5, 3, 4, 1], ![2, 6, 5, 3, 4, 0], ![1, 0, 6, 5, 3, 4], ![6, 5, 1, 0, 2, 4], ![6, 5, 1, 0, 2, 3], ![6, 4, 3, 1, 0, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 134 }

theorem namedLeaf007_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18055)) namedLeaf007 = true :=
  by decide +kernel

def namedLeaf008 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 5, 6], ![1, 0, 3, 2, 5, 6], ![1, 0, 2, 3, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 100 }

theorem namedLeaf008_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18056)) namedLeaf008 = true :=
  by decide +kernel

def namedLeaf009 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 5, 6], ![1, 0, 3, 2, 6, 5], ![1, 0, 2, 3, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 146 }

theorem namedLeaf009_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18057)) namedLeaf009 = true :=
  by decide +kernel

def namedLeaf010 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 5, 6], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![1, 0, 2, 6, 3, 4], ![1, 0, 2, 5, 3, 4]], proof := .tail 174 }

theorem namedLeaf010_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18058)) namedLeaf010 = true :=
  by decide +kernel

def namedLeaf011 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 2, 3, 4]], proof := .low (![231, 194, 301, 247, 201, 358, 360, 264, 322, 285, 183, 171, 117, 219, 52, 147, 172, 361, 370, 1, 314, 20, 253, 148, 274, 38, 214, 220]) }

theorem namedLeaf011_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18059)) namedLeaf011 = true :=
  by decide +kernel

def namedLeaf012 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 2, 3, 4]], proof := .low (![249, 353, 354, 233, 133, 358, 75, 56, 45, 263, 294, 239, 335, 206, 336, 163, 172, 232, 244, 319, 270, 161, 342, 63, 166, 38, 18, 296]) }

theorem namedLeaf012_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18060)) namedLeaf012 = true :=
  by decide +kernel

def namedLeaf013 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 3, 6, 5], ![1, 0, 4, 2, 6, 5], ![1, 0, 3, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 2, 3, 4]], proof := .low (![231, 259, 55, 156, 169, 157, 265, 34, 286, 211, 86, 57, 376, 223, 350, 191, 172, 97, 303, 142, 137, 346, 321, 13, 325, 371, 278, 176]) }

theorem namedLeaf013_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18061)) namedLeaf013 = true :=
  by decide +kernel

def namedLeaf014 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 3, 2, 4]], proof := .low (![372, 315, 62, 49, 121, 358, 360, 366, 70, 197, 200, 64, 117, 84, 21, 147, 104, 104, 198, 1, 116, 24, 253, 131, 234, 38, 214, 220]) }

theorem namedLeaf014_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18062)) namedLeaf014 = true :=
  by decide +kernel

def namedLeaf015 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 3, 4, 2]], proof := .tail 307 }

theorem namedLeaf015_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18063)) namedLeaf015 = true :=
  by decide +kernel

def namedLeaf016 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![1, 0, 6, 2, 3, 4], ![1, 0, 5, 4, 3, 2]], proof := .tail 215 }

theorem namedLeaf016_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18064)) namedLeaf016 = true :=
  by decide +kernel

def namedLeaf017 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 3, 2, 4]], proof := .low (![372, 315, 62, 275, 133, 28, 181, 366, 70, 197, 257, 64, 112, 282, 21, 298, 104, 232, 238, 298, 116, 222, 298, 234, 217, 38, 90, 10]) }

theorem namedLeaf017_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18065)) namedLeaf017 = true :=
  by decide +kernel

def namedLeaf018 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 3, 4, 2]], proof := .tail 307 }

theorem namedLeaf018_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18066)) namedLeaf018 = true :=
  by decide +kernel

def namedLeaf019 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 0, 4, 3, 2]], proof := .tail 154 }

theorem namedLeaf019_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18067)) namedLeaf019 = true :=
  by decide +kernel

def namedLeaf020 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 0, 3, 2]], proof := .tail 154 }

theorem namedLeaf020_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18068)) namedLeaf020 = true :=
  by decide +kernel

def namedLeaf021 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 6, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 2, 6, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 3, 2, 4]], proof := .low (![372, 245, 359, 74, 169, 281, 126, 320, 210, 185, 86, 108, 224, 223, 350, 191, 326, 337, 303, 142, 137, 177, 321, 13, 83, 371, 278, 125]) }

theorem namedLeaf021_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18069)) namedLeaf021 = true :=
  by decide +kernel

def namedLeaf022 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 4, 6, 2, 5], ![1, 0, 3, 6, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 307 }

theorem namedLeaf022_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18070)) namedLeaf022 = true :=
  by decide +kernel

def namedLeaf023 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 0, 6, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 0, 4, 3, 2]], proof := .tail 59 }

theorem namedLeaf023_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18071)) namedLeaf023 = true :=
  by decide +kernel

def namedLeaf024 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 0, 3, 2]], proof := .tail 345 }

theorem namedLeaf024_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18072)) namedLeaf024 = true :=
  by decide +kernel

def namedLeaf025 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 0, 6, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 170 }

theorem namedLeaf025_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18073)) namedLeaf025 = true :=
  by decide +kernel

def namedLeaf026 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![1, 6, 0, 2, 3, 4], ![1, 5, 4, 3, 0, 2]], proof := .tail 0 }

theorem namedLeaf026_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18074)) namedLeaf026 = true :=
  by decide +kernel

def namedLeaf027 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![1, 6, 0, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 0 }

theorem namedLeaf027_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18075)) namedLeaf027 = true :=
  by decide +kernel

def namedLeaf028 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 3, 5], ![1, 6, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 0 }

theorem namedLeaf028_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18076)) namedLeaf028 = true :=
  by decide +kernel

def namedLeaf029 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 4, 3, 5], ![6, 1, 0, 4, 2, 5], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 2, 3, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 60 }

theorem namedLeaf029_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18077)) namedLeaf029 = true :=
  by decide +kernel

def namedLeaf030 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 2, 6], ![1, 0, 3, 2, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![331, 194, 301, 266, 79, 358, 360, 264, 322, 119, 72, 171, 117, 219, 190, 99, 31, 361, 373, 130, 314, 20, 277, 148, 14, 38, 153, 220]) }

theorem namedLeaf030_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18078)) namedLeaf030 = true :=
  by decide +kernel

def namedLeaf031 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 3, 6], ![1, 0, 4, 5, 2, 6], ![1, 0, 3, 2, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 2, 3, 5, 4]], proof := .tail 291 }

theorem namedLeaf031_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18079)) namedLeaf031 = true :=
  by decide +kernel

def namedLeaf032 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 0, 4, 5, 2, 6], ![1, 0, 3, 5, 2, 6], ![1, 0, 3, 4, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 310 }

theorem namedLeaf032_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18080)) namedLeaf032 = true :=
  by decide +kernel

def namedLeaf033 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 2, 6], ![1, 0, 5, 3, 2, 6], ![1, 0, 4, 3, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 242 }

theorem namedLeaf033_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18081)) namedLeaf033 = true :=
  by decide +kernel

def namedLeaf034 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 2, 6], ![1, 5, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .tail 58 }

theorem namedLeaf034_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18082)) namedLeaf034 = true :=
  by decide +kernel

def namedLeaf035 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 4, 3, 6], ![1, 0, 5, 4, 2, 6], ![5, 1, 0, 3, 2, 6], ![4, 1, 0, 3, 2, 6], ![1, 0, 2, 3, 4, 5]], proof := .low (![101, 240, 30, 102, 355, 11, 292, 9, 324, 103, 22, 171, 205, 213, 295, 111, 165, 42, 71, 228, 374, 308, 323, 43, 357, 15, 204, 250]) }

theorem namedLeaf035_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18083)) namedLeaf035 = true :=
  by decide +kernel

def namedLeaf036 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 5, 6], ![1, 0, 3, 2, 4, 6], ![1, 0, 3, 2, 4, 5]], proof := .low (![273, 194, 301, 266, 79, 358, 360, 264, 322, 119, 72, 327, 117, 219, 190, 99, 120, 361, 373, 130, 314, 20, 277, 148, 14, 38, 153, 220]) }

theorem namedLeaf036_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18084)) namedLeaf036 = true :=
  by decide +kernel

def namedLeaf037 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 5, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 6, 5], ![1, 0, 3, 2, 6, 4], ![1, 0, 3, 2, 5, 4]], proof := .low (![150, 194, 301, 247, 79, 358, 360, 264, 322, 285, 72, 312, 117, 219, 52, 99, 363, 361, 370, 130, 314, 20, 277, 148, 274, 38, 153, 220]) }

theorem namedLeaf037_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18085)) namedLeaf037 = true :=
  by decide +kernel

def namedLeaf038 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 2, 6, 5], ![1, 0, 3, 6, 2, 4], ![1, 0, 3, 5, 2, 4]], proof := .low (![241, 212, 301, 272, 201, 358, 360, 251, 322, 98, 183, 339, 117, 219, 52, 147, 41, 122, 370, 1, 314, 20, 253, 148, 274, 38, 214, 220]) }

theorem namedLeaf038_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18086)) namedLeaf038 = true :=
  by decide +kernel

def namedLeaf039 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 2, 6, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 3, 2, 4]], proof := .low (![180, 236, 258, 230, 40, 358, 360, 341, 107, 347, 183, 237, 117, 159, 367, 147, 202, 361, 47, 1, 207, 225, 253, 73, 73, 38, 214, 220]) }

theorem namedLeaf039_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18087)) namedLeaf039 = true :=
  by decide +kernel

def namedLeaf040 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 2, 6, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 3, 2, 4]], proof := .low (![95, 236, 258, 230, 133, 358, 181, 341, 107, 347, 192, 246, 335, 48, 73, 252, 202, 232, 290, 26, 48, 222, 155, 73, 217, 38, 90, 10]) }

theorem namedLeaf040_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18088)) namedLeaf040 = true :=
  by decide +kernel

def namedLeaf041 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 4, 6, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 2, 6, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 3, 2, 4]], proof := .low (![302, 259, 328, 156, 169, 66, 280, 34, 286, 211, 86, 57, 369, 223, 350, 191, 209, 97, 303, 142, 137, 177, 321, 13, 325, 371, 278, 127]) }

theorem namedLeaf041_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18089)) namedLeaf041 = true :=
  by decide +kernel

def namedLeaf042 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 6, 2, 5], ![1, 0, 3, 6, 2, 4], ![1, 0, 3, 5, 4, 2]], proof := .tail 307 }

theorem namedLeaf042_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18090)) namedLeaf042 = true :=
  by decide +kernel

def namedLeaf043 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 2, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 3, 4, 2]], proof := .tail 307 }

theorem namedLeaf043_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18091)) namedLeaf043 = true :=
  by decide +kernel

def namedLeaf044 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 3, 4, 2]], proof := .tail 307 }

theorem namedLeaf044_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18092)) namedLeaf044 = true :=
  by decide +kernel

def namedLeaf045 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 3, 4, 2]], proof := .tail 307 }

theorem namedLeaf045_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18093)) namedLeaf045 = true :=
  by decide +kernel

def namedLeaf046 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 2, 5], ![1, 0, 6, 3, 2, 4], ![1, 0, 5, 4, 3, 2]], proof := .tail 364 }

theorem namedLeaf046_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18094)) namedLeaf046 = true :=
  by decide +kernel

def namedLeaf047 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 0, 4, 3, 2]], proof := .tail 364 }

theorem namedLeaf047_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18095)) namedLeaf047 = true :=
  by decide +kernel

def namedLeaf048 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 0, 4, 3, 2]], proof := .tail 364 }

theorem namedLeaf048_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18096)) namedLeaf048 = true :=
  by decide +kernel

def namedLeaf049 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 6, 0, 3, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 4, 0, 3, 2]], proof := .tail 364 }

theorem namedLeaf049_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18097)) namedLeaf049 = true :=
  by decide +kernel

def namedLeaf050 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![1, 6, 0, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 4, 0, 3, 2]], proof := .tail 364 }

theorem namedLeaf050_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18098)) namedLeaf050 = true :=
  by decide +kernel

def namedLeaf051 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 0, 6, 4, 5, 2], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 1, 0, 3, 2]], proof := .tail 364 }

theorem namedLeaf051_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18099)) namedLeaf051 = true :=
  by decide +kernel

def namedLeaf052 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 5, 2, 6], ![1, 0, 3, 4, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .tail 310 }

theorem namedLeaf052_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18100)) namedLeaf052 = true :=
  by decide +kernel

def namedLeaf053 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 5, 6, 2], ![1, 0, 3, 4, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 17 }

theorem namedLeaf053_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18101)) namedLeaf053 = true :=
  by decide +kernel

def namedLeaf054 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 5, 6, 2], ![1, 0, 3, 4, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 317 }

theorem namedLeaf054_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18102)) namedLeaf054 = true :=
  by decide +kernel

def namedLeaf055 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 5, 6, 2], ![1, 0, 3, 6, 5, 2], ![1, 0, 3, 6, 4, 2], ![1, 0, 3, 5, 4, 2]], proof := .tail 221 }

theorem namedLeaf055_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18103)) namedLeaf055 = true :=
  by decide +kernel

def namedLeaf056 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 5, 2], ![1, 0, 6, 3, 4, 2], ![1, 0, 5, 3, 4, 2]], proof := .tail 362 }

theorem namedLeaf056_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18104)) namedLeaf056 = true :=
  by decide +kernel

def namedLeaf057 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 0, 3, 4, 2]], proof := .tail 362 }

theorem namedLeaf057_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18105)) namedLeaf057 = true :=
  by decide +kernel

def namedLeaf058 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 4, 6, 5, 2], ![1, 0, 3, 6, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 0, 3, 4, 2]], proof := .tail 362 }

theorem namedLeaf058_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18106)) namedLeaf058 = true :=
  by decide +kernel

def namedLeaf059 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 5, 2], ![1, 0, 6, 3, 4, 2], ![1, 0, 5, 4, 3, 2]], proof := .tail 300 }

theorem namedLeaf059_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18107)) namedLeaf059 = true :=
  by decide +kernel

def namedLeaf060 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 0, 4, 3, 2]], proof := .tail 255 }

theorem namedLeaf060_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18108)) namedLeaf060 = true :=
  by decide +kernel

def namedLeaf061 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 0, 6, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 0, 4, 3, 2]], proof := .tail 113 }

theorem namedLeaf061_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18109)) namedLeaf061 = true :=
  by decide +kernel

def namedLeaf062 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 6, 0, 3, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 4, 0, 3, 2]], proof := .tail 44 }

theorem namedLeaf062_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18110)) namedLeaf062 = true :=
  by decide +kernel

def namedLeaf063 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![1, 6, 0, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 4, 0, 3, 2]], proof := .tail 44 }

theorem namedLeaf063_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18111)) namedLeaf063 = true :=
  by decide +kernel

def namedLeaf064 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 4, 5, 2], ![6, 1, 0, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 229 }

theorem namedLeaf064_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18112)) namedLeaf064 = true :=
  by decide +kernel

def namedLeaf065 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![1, 0, 5, 3, 2, 6], ![1, 0, 4, 3, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .low (![67, 94, 268, 247, 79, 358, 360, 132, 208, 285, 72, 65, 117, 12, 52, 99, 3, 195, 370, 130, 188, 349, 277, 148, 274, 38, 153, 220]) }

theorem namedLeaf065_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18113)) namedLeaf065 = true :=
  by decide +kernel

def namedLeaf066 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 4, 6, 2], ![1, 0, 5, 3, 6, 2], ![1, 0, 4, 3, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 80 }

theorem namedLeaf066_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18114)) namedLeaf066 = true :=
  by decide +kernel

def namedLeaf067 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 4, 6, 2], ![1, 0, 5, 3, 6, 2], ![1, 0, 4, 3, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 271 }

theorem namedLeaf067_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18115)) namedLeaf067 = true :=
  by decide +kernel

def namedLeaf068 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 0, 5, 6, 3, 2], ![1, 0, 4, 3, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .low (![276, 135, 141, 199, 160, 358, 360, 267, 4, 53, 183, 76, 117, 311, 52, 147, 89, 37, 370, 1, 46, 365, 253, 148, 274, 38, 214, 220]) }

theorem namedLeaf068_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18116)) namedLeaf068 = true :=
  by decide +kernel

def namedLeaf069 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 0, 5, 6, 3, 2], ![1, 0, 4, 3, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 96 }

theorem namedLeaf069_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18117)) namedLeaf069 = true :=
  by decide +kernel

def namedLeaf070 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 5, 6, 3, 2], ![1, 0, 4, 6, 3, 2], ![1, 0, 4, 5, 3, 2]], proof := .tail 173 }

theorem namedLeaf070_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18118)) namedLeaf070 = true :=
  by decide +kernel

def namedLeaf071 : LeafData := { rows := ![![2, 3, 4, 5, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 6, 5, 3, 2], ![1, 0, 6, 4, 3, 2], ![1, 0, 5, 4, 3, 2]], proof := .tail 305 }

theorem namedLeaf071_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18119)) namedLeaf071 = true :=
  by decide +kernel

def namedLeaf072 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 6, 5, 3, 2], ![1, 6, 0, 4, 3, 2], ![1, 5, 0, 4, 3, 2]], proof := .tail 69 }

theorem namedLeaf072_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18120)) namedLeaf072 = true :=
  by decide +kernel

def namedLeaf073 : LeafData := { rows := ![![2, 3, 4, 6, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 0, 6, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 1, 0, 4, 3, 2]], proof := .tail 216 }

theorem namedLeaf073_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18121)) namedLeaf073 = true :=
  by decide +kernel

def namedLeaf074 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 6, 0, 5, 3, 2], ![1, 6, 0, 4, 3, 2], ![1, 5, 4, 0, 3, 2]], proof := .tail 151 }

theorem namedLeaf074_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18122)) namedLeaf074 = true :=
  by decide +kernel

def namedLeaf075 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 6, 0, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 1, 4, 0, 3, 2]], proof := .tail 151 }

theorem namedLeaf075_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18123)) namedLeaf075 = true :=
  by decide +kernel

def namedLeaf076 : LeafData := { rows := ![![2, 3, 6, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![6, 1, 0, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 19 }

theorem namedLeaf076_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18124)) namedLeaf076 = true :=
  by decide +kernel

def namedLeaf077 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![1, 5, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .low (![67, 94, 268, 16, 79, 28, 39, 132, 208, 175, 183, 158, 25, 12, 235, 147, 3, 297, 23, 1, 349, 105, 277, 148, 334, 38, 214, 333]) }

theorem namedLeaf077_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18125)) namedLeaf077 = true :=
  by decide +kernel

def namedLeaf078 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 4, 6, 2], ![1, 5, 0, 3, 6, 2], ![1, 4, 0, 3, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 256 }

theorem namedLeaf078_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18126)) namedLeaf078 = true :=
  by decide +kernel

def namedLeaf079 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 5, 0, 6, 3, 2], ![1, 4, 0, 3, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 35 }

theorem namedLeaf079_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18127)) namedLeaf079 = true :=
  by decide +kernel

def namedLeaf080 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 4, 6, 2], ![1, 5, 0, 3, 6, 2], ![1, 4, 0, 3, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 284 }

theorem namedLeaf080_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18128)) namedLeaf080 = true :=
  by decide +kernel

def namedLeaf081 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 5, 0, 6, 3, 2], ![1, 4, 0, 3, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 35 }

theorem namedLeaf081_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18129)) namedLeaf081 = true :=
  by decide +kernel

def namedLeaf082 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 5, 0, 6, 3, 2], ![1, 4, 0, 6, 3, 2], ![1, 0, 4, 5, 3, 2]], proof := .tail 173 }

theorem namedLeaf082_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18130)) namedLeaf082 = true :=
  by decide +kernel

def namedLeaf083 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .low (![276, 135, 50, 16, 254, 358, 140, 267, 4, 144, 2, 91, 109, 365, 139, 344, 89, 279, 178, 8, 365, 375, 110, 148, 288, 38, 243, 179]) }

theorem namedLeaf083_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18131)) namedLeaf083 = true :=
  by decide +kernel

def namedLeaf084 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 0, 3, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 82 }

theorem namedLeaf084_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18132)) namedLeaf084 = true :=
  by decide +kernel

def namedLeaf085 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 0, 6, 3, 2], ![1, 4, 0, 5, 3, 2]], proof := .tail 173 }

theorem namedLeaf085_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18133)) namedLeaf085 = true :=
  by decide +kernel

def namedLeaf086 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 6, 0, 3, 2], ![1, 4, 5, 0, 3, 2]], proof := .tail 173 }

theorem namedLeaf086_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18134)) namedLeaf086 = true :=
  by decide +kernel

def namedLeaf087 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 6, 5, 0, 3, 2], ![1, 6, 4, 0, 3, 2], ![1, 5, 4, 0, 3, 2]], proof := .tail 69 }

theorem namedLeaf087_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18135)) namedLeaf087 = true :=
  by decide +kernel

def namedLeaf088 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![1, 6, 5, 0, 3, 2], ![6, 1, 4, 0, 3, 2], ![5, 1, 4, 0, 3, 2]], proof := .tail 152 }

theorem namedLeaf088_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18136)) namedLeaf088 = true :=
  by decide +kernel

def namedLeaf089 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![6, 1, 5, 0, 3, 2], ![6, 1, 4, 0, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 283 }

theorem namedLeaf089_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18137)) namedLeaf089 = true :=
  by decide +kernel

def namedLeaf090 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 4, 6, 3], ![1, 0, 5, 4, 6, 2], ![5, 1, 0, 3, 2, 6], ![4, 1, 0, 3, 2, 6], ![1, 0, 3, 2, 4, 5]], proof := .low (![101, 240, 368, 102, 355, 11, 292, 9, 324, 103, 22, 171, 205, 196, 295, 111, 340, 42, 71, 228, 374, 306, 323, 43, 357, 15, 204, 250]) }

theorem namedLeaf090_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18138)) namedLeaf090 = true :=
  by decide +kernel

def namedLeaf091 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 4, 6, 2], ![5, 1, 0, 3, 6, 2], ![4, 1, 0, 3, 2, 6], ![1, 0, 3, 4, 2, 5]], proof := .tail 167 }

theorem namedLeaf091_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18139)) namedLeaf091 = true :=
  by decide +kernel

def namedLeaf092 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 1, 0, 3, 2, 6], ![1, 0, 4, 3, 2, 5]], proof := .tail 29 }

theorem namedLeaf092_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18140)) namedLeaf092 = true :=
  by decide +kernel

def namedLeaf093 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 4, 6, 2], ![5, 1, 0, 3, 6, 2], ![4, 1, 0, 3, 6, 2], ![1, 0, 3, 4, 5, 2]], proof := .tail 348 }

theorem namedLeaf093_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18141)) namedLeaf093 = true :=
  by decide +kernel

def namedLeaf094 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 1, 0, 3, 6, 2], ![1, 0, 4, 3, 5, 2]], proof := .tail 29 }

theorem namedLeaf094_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18142)) namedLeaf094 = true :=
  by decide +kernel

def namedLeaf095 : LeafData := { rows := ![![2, 3, 5, 4, 6, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 1, 0, 6, 3, 2], ![4, 1, 0, 6, 3, 2], ![1, 0, 4, 5, 3, 2]], proof := .tail 318 }

theorem namedLeaf095_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18143)) namedLeaf095 = true :=
  by decide +kernel

def namedLeaf096 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 0, 3, 2, 6], ![1, 4, 0, 3, 2, 5]], proof := .tail 29 }

theorem namedLeaf096_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18144)) namedLeaf096 = true :=
  by decide +kernel

def namedLeaf097 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 0, 3, 6, 2], ![1, 4, 0, 3, 5, 2]], proof := .tail 29 }

theorem namedLeaf097_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18145)) namedLeaf097 = true :=
  by decide +kernel

def namedLeaf098 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 0, 6, 3, 2], ![1, 4, 0, 5, 3, 2]], proof := .tail 318 }

theorem namedLeaf098_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18146)) namedLeaf098 = true :=
  by decide +kernel

def namedLeaf099 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 6, 0, 3, 2], ![1, 4, 5, 0, 3, 2]], proof := .tail 318 }

theorem namedLeaf099_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18147)) namedLeaf099 = true :=
  by decide +kernel

def namedLeaf100 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 5, 6, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 0, 3, 2, 6], ![4, 1, 0, 3, 2, 5]], proof := .low (![114, 138, 218, 269, 316, 203, 260, 168, 81, 248, 7, 343, 136, 27, 162, 92, 33, 184, 128, 287, 309, 261, 289, 36, 149, 143, 5, 189]) }

theorem namedLeaf100_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18148)) namedLeaf100 = true :=
  by decide +kernel

def namedLeaf101 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 5, 6, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 0, 3, 6, 2], ![4, 1, 0, 3, 5, 2]], proof := .tail 82 }

theorem namedLeaf101_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18149)) namedLeaf101 = true :=
  by decide +kernel

def namedLeaf102 : LeafData := { rows := ![![2, 3, 5, 6, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 0, 6, 3, 2], ![4, 1, 0, 5, 3, 2]], proof := .tail 87 }

theorem namedLeaf102_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18150)) namedLeaf102 = true :=
  by decide +kernel

def namedLeaf103 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 6, 0, 3, 2], ![4, 1, 5, 0, 3, 2]], proof := .tail 87 }

theorem namedLeaf103_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18151)) namedLeaf103 = true :=
  by decide +kernel

def namedLeaf104 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 1, 0, 3, 2], ![4, 5, 1, 0, 3, 2]], proof := .tail 87 }

theorem namedLeaf104_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18152)) namedLeaf104 = true :=
  by decide +kernel

def namedLeaf105 : LeafData := { rows := ![![2, 3, 6, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 0, 6, 5, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 1, 0, 3, 2], ![5, 4, 1, 0, 3, 2]], proof := .tail 186 }

theorem namedLeaf105_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18153)) namedLeaf105 = true :=
  by decide +kernel

def namedLeaf106 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 0, 4, 5, 2], ![1, 6, 0, 3, 2, 5], ![1, 6, 0, 3, 2, 4], ![1, 5, 4, 3, 0, 2]], proof := .tail 118 }

theorem namedLeaf106_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18154)) namedLeaf106 = true :=
  by decide +kernel

def namedLeaf107 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 4, 5, 2], ![1, 6, 0, 3, 5, 2], ![1, 6, 0, 3, 4, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 106 }

theorem namedLeaf107_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18155)) namedLeaf107 = true :=
  by decide +kernel

def namedLeaf108 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![1, 6, 0, 5, 3, 2], ![1, 6, 0, 4, 3, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 151 }

theorem namedLeaf108_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18156)) namedLeaf108 = true :=
  by decide +kernel

def namedLeaf109 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![1, 5, 6, 0, 3, 2], ![1, 4, 6, 0, 3, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 77 }

theorem namedLeaf109_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18157)) namedLeaf109 = true :=
  by decide +kernel

def namedLeaf110 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 5, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![1, 6, 5, 0, 3, 2], ![1, 6, 4, 0, 3, 2], ![1, 5, 4, 3, 0, 2]], proof := .tail 164 }

theorem namedLeaf110_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18158)) namedLeaf110 = true :=
  by decide +kernel

def namedLeaf111 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 5, 4, 6, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![5, 1, 6, 0, 3, 2], ![4, 1, 6, 0, 3, 2], ![1, 4, 5, 3, 0, 2]], proof := .tail 293 }

theorem namedLeaf111_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18159)) namedLeaf111 = true :=
  by decide +kernel

def namedLeaf112 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 0, 4, 5, 2], ![1, 6, 0, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 1, 4, 3, 0, 2]], proof := .tail 118 }

theorem namedLeaf112_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18160)) namedLeaf112 = true :=
  by decide +kernel

def namedLeaf113 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 4, 5, 2], ![1, 6, 0, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 106 }

theorem namedLeaf113_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18161)) namedLeaf113 = true :=
  by decide +kernel

def namedLeaf114 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![1, 6, 0, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 151 }

theorem namedLeaf114_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18162)) namedLeaf114 = true :=
  by decide +kernel

def namedLeaf115 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 4, 6, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![1, 6, 5, 0, 3, 2], ![6, 1, 4, 0, 3, 2], ![5, 1, 4, 3, 0, 2]], proof := .tail 164 }

theorem namedLeaf115_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18163)) namedLeaf115 = true :=
  by decide +kernel

def namedLeaf116 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 5, 6, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 1, 6, 0, 3, 2], ![4, 1, 5, 3, 0, 2]], proof := .tail 164 }

theorem namedLeaf116_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18164)) namedLeaf116 = true :=
  by decide +kernel

def namedLeaf117 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 4, 5, 3], ![1, 6, 0, 4, 5, 2], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 1, 3, 0, 2]], proof := .tail 118 }

theorem namedLeaf117_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18165)) namedLeaf117 = true :=
  by decide +kernel

def namedLeaf118 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 4, 5, 2], ![6, 1, 0, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 106 }

theorem namedLeaf118_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18166)) namedLeaf118 = true :=
  by decide +kernel

def namedLeaf119 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![6, 1, 0, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 88 }

theorem namedLeaf119_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18167)) namedLeaf119 = true :=
  by decide +kernel

def namedLeaf120 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![6, 1, 5, 0, 3, 2], ![6, 1, 4, 0, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 164 }

theorem namedLeaf120_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18168)) namedLeaf120 = true :=
  by decide +kernel

def namedLeaf121 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 1, 0, 3, 2], ![4, 5, 1, 3, 0, 2]], proof := .tail 164 }

theorem namedLeaf121_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18169)) namedLeaf121 = true :=
  by decide +kernel

def namedLeaf122 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 3, 6, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![1, 6, 0, 5, 4, 2], ![6, 5, 1, 0, 3, 2], ![6, 4, 1, 0, 3, 2], ![5, 4, 1, 3, 0, 2]], proof := .tail 164 }

theorem namedLeaf122_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18170)) namedLeaf122 = true :=
  by decide +kernel

def namedLeaf123 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 4, 5, 3], ![6, 1, 0, 4, 5, 2], ![6, 1, 0, 3, 2, 5], ![6, 1, 0, 3, 2, 4], ![5, 4, 3, 1, 0, 2]], proof := .tail 6 }

theorem namedLeaf123_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18171)) namedLeaf123 = true :=
  by decide +kernel

def namedLeaf124 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 4, 5, 2], ![6, 1, 0, 3, 5, 2], ![6, 1, 0, 3, 4, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 124 }

theorem namedLeaf124_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18172)) namedLeaf124 = true :=
  by decide +kernel

def namedLeaf125 : LeafData := { rows := ![![2, 6, 3, 4, 5, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![6, 1, 0, 5, 3, 2], ![6, 1, 0, 4, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 182 }

theorem namedLeaf125_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18173)) namedLeaf125 = true :=
  by decide +kernel

def namedLeaf126 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 4, 5, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![6, 1, 5, 0, 3, 2], ![6, 1, 4, 0, 3, 2], ![5, 4, 3, 1, 0, 2]], proof := .tail 283 }

theorem namedLeaf126_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18174)) namedLeaf126 = true :=
  by decide +kernel

def namedLeaf127 : LeafData := { rows := ![![2, 6, 3, 5, 4, 1], ![2, 6, 3, 5, 4, 0], ![1, 0, 6, 5, 4, 3], ![6, 1, 0, 5, 4, 2], ![5, 6, 1, 0, 3, 2], ![4, 6, 1, 0, 3, 2], ![4, 5, 3, 1, 0, 2]], proof := .tail 227 }

theorem namedLeaf127_checked :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 18175)) namedLeaf127 = true :=
  by decide +kernel

def fallback : LeafData := { rows := fun _ _ => 0, proof := .tail 0 }
def lookup (offset : ℕ) : LeafData :=
  if offset < 128 then (if offset < 64 then (if offset < 32 then (if offset < 16 then (if offset < 8 then (if offset < 4 then (if offset < 2 then (if offset < 1 then (namedLeaf000) else (namedLeaf001)) else (if offset < 3 then (namedLeaf002) else (namedLeaf003))) else (if offset < 6 then (if offset < 5 then (namedLeaf004) else (namedLeaf005)) else (if offset < 7 then (namedLeaf006) else (namedLeaf007)))) else (if offset < 12 then (if offset < 10 then (if offset < 9 then (namedLeaf008) else (namedLeaf009)) else (if offset < 11 then (namedLeaf010) else (namedLeaf011))) else (if offset < 14 then (if offset < 13 then (namedLeaf012) else (namedLeaf013)) else (if offset < 15 then (namedLeaf014) else (namedLeaf015))))) else (if offset < 24 then (if offset < 20 then (if offset < 18 then (if offset < 17 then (namedLeaf016) else (namedLeaf017)) else (if offset < 19 then (namedLeaf018) else (namedLeaf019))) else (if offset < 22 then (if offset < 21 then (namedLeaf020) else (namedLeaf021)) else (if offset < 23 then (namedLeaf022) else (namedLeaf023)))) else (if offset < 28 then (if offset < 26 then (if offset < 25 then (namedLeaf024) else (namedLeaf025)) else (if offset < 27 then (namedLeaf026) else (namedLeaf027))) else (if offset < 30 then (if offset < 29 then (namedLeaf028) else (namedLeaf029)) else (if offset < 31 then (namedLeaf030) else (namedLeaf031)))))) else (if offset < 48 then (if offset < 40 then (if offset < 36 then (if offset < 34 then (if offset < 33 then (namedLeaf032) else (namedLeaf033)) else (if offset < 35 then (namedLeaf034) else (namedLeaf035))) else (if offset < 38 then (if offset < 37 then (namedLeaf036) else (namedLeaf037)) else (if offset < 39 then (namedLeaf038) else (namedLeaf039)))) else (if offset < 44 then (if offset < 42 then (if offset < 41 then (namedLeaf040) else (namedLeaf041)) else (if offset < 43 then (namedLeaf042) else (namedLeaf043))) else (if offset < 46 then (if offset < 45 then (namedLeaf044) else (namedLeaf045)) else (if offset < 47 then (namedLeaf046) else (namedLeaf047))))) else (if offset < 56 then (if offset < 52 then (if offset < 50 then (if offset < 49 then (namedLeaf048) else (namedLeaf049)) else (if offset < 51 then (namedLeaf050) else (namedLeaf051))) else (if offset < 54 then (if offset < 53 then (namedLeaf052) else (namedLeaf053)) else (if offset < 55 then (namedLeaf054) else (namedLeaf055)))) else (if offset < 60 then (if offset < 58 then (if offset < 57 then (namedLeaf056) else (namedLeaf057)) else (if offset < 59 then (namedLeaf058) else (namedLeaf059))) else (if offset < 62 then (if offset < 61 then (namedLeaf060) else (namedLeaf061)) else (if offset < 63 then (namedLeaf062) else (namedLeaf063))))))) else (if offset < 96 then (if offset < 80 then (if offset < 72 then (if offset < 68 then (if offset < 66 then (if offset < 65 then (namedLeaf064) else (namedLeaf065)) else (if offset < 67 then (namedLeaf066) else (namedLeaf067))) else (if offset < 70 then (if offset < 69 then (namedLeaf068) else (namedLeaf069)) else (if offset < 71 then (namedLeaf070) else (namedLeaf071)))) else (if offset < 76 then (if offset < 74 then (if offset < 73 then (namedLeaf072) else (namedLeaf073)) else (if offset < 75 then (namedLeaf074) else (namedLeaf075))) else (if offset < 78 then (if offset < 77 then (namedLeaf076) else (namedLeaf077)) else (if offset < 79 then (namedLeaf078) else (namedLeaf079))))) else (if offset < 88 then (if offset < 84 then (if offset < 82 then (if offset < 81 then (namedLeaf080) else (namedLeaf081)) else (if offset < 83 then (namedLeaf082) else (namedLeaf083))) else (if offset < 86 then (if offset < 85 then (namedLeaf084) else (namedLeaf085)) else (if offset < 87 then (namedLeaf086) else (namedLeaf087)))) else (if offset < 92 then (if offset < 90 then (if offset < 89 then (namedLeaf088) else (namedLeaf089)) else (if offset < 91 then (namedLeaf090) else (namedLeaf091))) else (if offset < 94 then (if offset < 93 then (namedLeaf092) else (namedLeaf093)) else (if offset < 95 then (namedLeaf094) else (namedLeaf095)))))) else (if offset < 112 then (if offset < 104 then (if offset < 100 then (if offset < 98 then (if offset < 97 then (namedLeaf096) else (namedLeaf097)) else (if offset < 99 then (namedLeaf098) else (namedLeaf099))) else (if offset < 102 then (if offset < 101 then (namedLeaf100) else (namedLeaf101)) else (if offset < 103 then (namedLeaf102) else (namedLeaf103)))) else (if offset < 108 then (if offset < 106 then (if offset < 105 then (namedLeaf104) else (namedLeaf105)) else (if offset < 107 then (namedLeaf106) else (namedLeaf107))) else (if offset < 110 then (if offset < 109 then (namedLeaf108) else (namedLeaf109)) else (if offset < 111 then (namedLeaf110) else (namedLeaf111))))) else (if offset < 120 then (if offset < 116 then (if offset < 114 then (if offset < 113 then (namedLeaf112) else (namedLeaf113)) else (if offset < 115 then (namedLeaf114) else (namedLeaf115))) else (if offset < 118 then (if offset < 117 then (namedLeaf116) else (namedLeaf117)) else (if offset < 119 then (namedLeaf118) else (namedLeaf119)))) else (if offset < 124 then (if offset < 122 then (if offset < 121 then (namedLeaf120) else (namedLeaf121)) else (if offset < 123 then (namedLeaf122) else (namedLeaf123))) else (if offset < 126 then (if offset < 125 then (namedLeaf124) else (namedLeaf125)) else (if offset < 127 then (namedLeaf126) else (namedLeaf127)))))))) else fallback

theorem point_checked (j : Fin 128) :
    leafCheck library (N4R2WordTree.catalog (Fin.ofNat 24698 (18048 + j.val))) (lookup j.val) = true := by
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

theorem correct (id : Fin 24698) (hlow : 18048 ≤ id.val) (hhigh : id.val < 18176) :
    leafCheck library (N4R2WordTree.catalog id) (lookup (id.val - 18048)) = true := by
  let j : Fin 128 := ⟨id.val - 18048, by omega⟩
  have hsum : 18048 + j.val = id.val := by dsimp [j]; omega
  have hindex : Fin.ofNat 24698 (18048 + j.val) = id := by
    apply Fin.ext
    simp only [Fin.ofNat, hsum, Nat.mod_eq_of_lt id.isLt]
  have hh := point_checked j
  rw [hindex] at hh
  exact hh

#print axioms point_checked
#print axioms correct
end Jsp404.N4R2OuterLeftData.LeafShard141
